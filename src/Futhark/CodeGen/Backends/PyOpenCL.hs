{-# LANGUAGE FlexibleContexts #-}
module Futhark.CodeGen.Backends.PyOpenCL
  ( compileProg
  ) where

import Control.Applicative
import Control.Monad
import Data.List

import Prelude
import NeatInterpolation()

import Futhark.Representation.ExplicitMemory (Prog)
import Futhark.CodeGen.Backends.PyOpenCL.Boilerplate
import qualified Futhark.CodeGen.Backends.GenericPython as Py
import qualified Futhark.CodeGen.ImpCode.OpenCL as Imp
import qualified Futhark.CodeGen.ImpGen.OpenCL as ImpGen
import Futhark.CodeGen.Backends.GenericPython.AST
import Futhark.Util.Pretty(pretty)
import Futhark.MonadFreshNames

import Futhark.CodeGen.Backends.GenericPython.Definitions


--maybe pass the config file rather than multiple arguments
compileProg :: MonadFreshNames m => Bool -> Bool -> Prog ->  m (Either String String)
compileProg timeit moduleConfig prog = do
  res <- ImpGen.compileProg prog
  --could probably be a better why do to this..
  let initCL = if moduleConfig then [] else [openClInit]
  let shebang = if moduleConfig then [] else ["#!/usr/bin/env python"]
  case res of
    Left err -> return $ Left err
    Right (Imp.Program opencl_code kernel_names prog')  -> do
      --prepare the strings for assigning the kernels and set them as global
      let assigned = map (\x -> Assign (Var (x++"_var")) (Var $ "program."++x)) kernel_names
      let assign_concat = intercalate "\n" $ map pretty assigned
      let kernel_declare = map (\x -> "global " ++ x ++ "_var") kernel_names
      let kernel_concat = intercalate "\n" kernel_declare

      let defines = [blockDimPragma, "ctx=0", "program=0", "queue=0", pyUtility, pyTestMain, openClDecls opencl_code assign_concat kernel_concat] ++ initCL
      let imports = shebang ++ ["import sys", "from numpy import *", "from ctypes import *", "import pyopencl as cl", "import time"]

      Right <$> Py.compileProg timeit imports defines operations () prog'
  where operations :: Py.Operations Imp.OpenCL ()
        operations = Py.Operations
                     { Py.opsCompiler = callKernel
                     , Py.opsWriteScalar = writeOpenCLScalar
                     , Py.opsReadScalar = readOpenCLScalar
                     , Py.opsAllocate = allocateOpenCLBuffer
                     , Py.opsCopy = copyOpenCLMemory
                     }

callKernel :: Py.OpCompiler Imp.OpenCL ()
callKernel (Imp.LaunchKernel name args kernel_size workgroup_size) = do
  kernel_size' <- mapM Py.compileExp kernel_size
  let total_elements = foldl mult_exp (Constant $ IntVal 1) kernel_size'
  let cond = BinaryOp "!=" total_elements (Constant $ IntVal 0)
  workgroup_size' <- case workgroup_size of
        Nothing -> return None
        Just es -> do size' <- mapM Py.compileExp es
                      return $ Tuple size'

  body <- Py.collect $ launchKernel name kernel_size' workgroup_size' args
  Py.stm $ If cond body [Pass]
  return Py.Done
  where mult_exp = BinaryOp "*"

launchKernel :: String -> [PyExp] -> PyExp -> [Imp.KernelArg] -> Py.CompilerM op s ()
launchKernel kernel_name kernel_dims workgroup_dims args = do
  let kernel_dims' = Tuple $ map Py.asscalar kernel_dims
  let kernel_name' = kernel_name ++ "_var"
  args' <- mapM processKernelArg args
  Py.stm $ Exp $ Call (kernel_name' ++ ".set_args") args'
  Py.stm $ Exp $ Call "cl.enqueue_nd_range_kernel" [Var "queue", Var kernel_name', kernel_dims', workgroup_dims]
  Py.stm $ Exp $ Call "queue.finish" []
  where processKernelArg :: Imp.KernelArg -> Py.CompilerM op s PyExp
        processKernelArg (Imp.ValueArg e bt) = do
          e' <- Py.compileExp e
          return $ Call (Py.compileBasicToNp bt) [e']
        processKernelArg (Imp.MemArg v) = return $ Var $ pretty v
        processKernelArg (Imp.SharedMemoryArg (Imp.Count num_bytes)) = do
          num_bytes' <- Py.compileExp num_bytes
          return $ Call "cl.LocalMemory" [num_bytes']

writeOpenCLScalar :: Py.WriteScalar Imp.OpenCL ()
writeOpenCLScalar mem i bt "device" val = do
  let mem' = Var $ pretty mem
  let nparr = Call "array" [val, ParamAssign (Var "dtype") (Var $ Py.compileBasicType bt)]
  Py.stm $ Exp $ Call "cl.enqueue_write_buffer" [Var "queue", mem', nparr, ParamAssign (Var "device_offset") i]
  Py.stm $ Exp $ Call "queue.finish" []

writeOpenCLScalar _ _ _ space _ =
  fail $ "Cannot write to '" ++ space ++ "' memory space."

readOpenCLScalar :: Py.ReadScalar Imp.OpenCL ()
readOpenCLScalar mem i bt "device" = do
  val <- newVName "read_res"
  let val' = Var $ pretty val
  let mem' = Var $ pretty mem
  let nparr = Call "empty" [Constant $ IntVal 1, ParamAssign (Var "dtype") (Var $ Py.compileBasicType bt)]
  let toNp = Py.asscalar i
  Py.stm $ Assign val' nparr
  Py.stm $ Exp $ Call "cl.enqueue_read_buffer" [Var "queue", mem', val', ParamAssign (Var "device_offset") toNp]
  Py.stm $ Exp $ Call "queue.finish" []
  return $ Index val' $ IdxExp $ Constant $ IntVal 0

readOpenCLScalar _ _ _ space =
  fail $ "Cannot read from '" ++ space ++ "' memory space."

allocateOpenCLBuffer :: Py.Allocate Imp.OpenCL ()
allocateOpenCLBuffer mem size "device" = do
  let toNp = Py.asscalar size
  let cond' = Cond (BinaryOp ">" size (Constant $ IntVal 0)) toNp (Constant $ IntVal 1)
  let call' = Call "cl.Buffer" [Var "ctx", Var "cl.mem_flags.READ_WRITE", cond']
  Py.stm $ Assign (Var $ pretty mem) call'

allocateOpenCLBuffer _ _ space =
  fail $ "Cannot allocate in '" ++ space ++ "' space"

copyOpenCLMemory :: Py.Copy Imp.OpenCL ()
copyOpenCLMemory destmem destidx Imp.DefaultSpace srcmem srcidx (Imp.Space "device") nbytes bt = do
  let srcmem'  = Var $ pretty srcmem
  let destmem' = Var $ pretty destmem
  let divide = BinaryOp "//" nbytes (Var $ Py.compileSizeOfType bt)
  let end = BinaryOp "+" destidx divide
  let dest = Index destmem' (IdxRange destidx end)
  Py.stm $ Exp $ Call "queue.finish" []
  Py.stm $ Exp $ Call "cl.enqueue_read_buffer" [Var "queue", srcmem', dest, ParamAssign (Var "device_offset") srcidx]

copyOpenCLMemory destmem destidx (Imp.Space "device") srcmem srcidx Imp.DefaultSpace nbytes bt = do
  let destmem' = Var $ pretty destmem
  let srcmem'  = Var $ pretty srcmem
  let divide = BinaryOp "//" nbytes (Var $ Py.compileSizeOfType bt)
  let end = BinaryOp "+" srcidx divide
  let src = Index srcmem' (IdxRange srcidx end)
  Py.stm $ Exp $ Call "queue.finish" []
  Py.stm $ Exp $ Call "cl.enqueue_write_buffer" [Var "queue", destmem', src, ParamAssign (Var "device_offset") destidx]

copyOpenCLMemory destmem destidx (Imp.Space "device") srcmem srcidx (Imp.Space "device") nbytes _ = do
  let destmem' = Var $ pretty destmem
  let srcmem'  = Var $ pretty srcmem
  let dest_offset = ParamAssign (Var "dst_offset") (Py.asscalar destidx)
  let src_offset = ParamAssign (Var "src_offset") (Py.asscalar srcidx)
  let bytecount = ParamAssign (Var "byte_count") (Py.asscalar nbytes)
  let cond = BinaryOp ">" nbytes (Constant $ IntVal 0)
  let tb = Exp $ Call "cl.enqueue_copy_buffer" [Var "queue", srcmem', destmem', dest_offset, src_offset, bytecount]
  Py.stm $ Exp $ Call "queue.finish" []
  Py.stm $ If cond [tb] [Pass]

copyOpenCLMemory _ _ destspace _ _ srcspace _ _=
  error $ "Cannot copy to " ++ show destspace ++ " from " ++ show srcspace

blockDimPragma :: String
blockDimPragma = "FUT_BLOCK_DIM = " ++ show (Imp.transposeBlockDim :: Int)
