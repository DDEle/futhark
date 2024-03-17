module Futhark.Test.WebGPUTest 
  ( generateTests
  )
where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text qualified as T
import Data.Map qualified as M
import Futhark.CodeGen.ImpCode.WebGPU
import Futhark.CodeGen.ImpGen.WebGPU (compileProg)
import Futhark.IR.GPUMem qualified as F
import Futhark.MonadFreshNames
import Futhark.Test.Spec
import Futhark.Test.Values qualified as V
import Futhark.Util.Pretty
import Data.Maybe (mapMaybe)
import Data.List (foldl')

generateTests :: (MonadFreshNames m, MonadIO m) =>
  FilePath -> F.Prog F.GPUMem -> m T.Text
generateTests path prog = do
  compiled <- snd <$> compileProg prog
  spec <- liftIO $ testSpecFromProgramOrDie (path <> ".fut")
  let tests = testCasesLiteral spec
  let info = kernelInfoLiteral compiled
  let shader = shaderLiteral compiled
  pure (tests <> "\n\n" <> info <> "\n\n" <> shader)

shaderLiteral :: Program -> T.Text
shaderLiteral prog = "window.shader = `\n"
  <> webgpuPrelude prog
  <> "\n"
  <> webgpuProgram prog
  <> "\n`;"

-- window.kernels = [
--   { name: 'some_vname_5568',
--     overrides: ['override', 'declarations'],
--     bindSlots: [0, 1, 2],
--   },
-- ];
kernelInfoLiteral :: Program -> T.Text
kernelInfoLiteral prog = "window.kernels = " <> docText fmtInfos <> ";"
  where
    infos = M.toList $ webgpuKernelInfo prog
    fmtInfos = "[" </> indent 2 (commastack $ map fmtInfo infos) </> "]"
    fmtInfo (name, (overrides, slots)) =
      "{" </> indent 2 (
        "name: '" <> pretty name <> "',"
        </> "overrides: [" <> commasep
          (map (\o -> "'" <> pretty o <> "'") overrides) <> "],"
        </> "bindSlots: " <> pretty slots <> ","
      ) </> "}"

-- window.tests = [
--   { entry: 'someName',
--     runs: [
--       {
--         inputTypes: ['i32'],
--         input: [[0, 1, 2, 3]],
--         expected: [[0, 2, 4, 6]],
--       },
--     ],
--   },
-- ];
testCasesLiteral :: ProgramTest -> T.Text
testCasesLiteral (ProgramTest _ _ (RunCases ios _ _)) =
  let specs = map ((<> ",\n") . prettyText . mkTestSpec) ios
   in "window.tests = [\n" <> foldl' (<>) "" specs <> "];"
testCasesLiteral t = "// Unsupported test: " <> testDescription t

data JsTestSpec = JsTestSpec 
  { jsEntryPoint :: T.Text,
    jsRuns :: [JsTestRun]
  }
data JsTestRun = JsTestRun
  { jsInputTypes :: [V.PrimType],
    jsInput :: [V.Value],
    jsExpected :: [V.Value]
  }

mkTestSpec :: InputOutputs -> JsTestSpec
mkTestSpec (InputOutputs entry runs) = JsTestSpec entry (mapMaybe mkRun runs)

mkRun :: TestRun -> Maybe JsTestRun
mkRun (TestRun _ (Values vals)
                 (Succeeds (Just (SuccessValues (Values expect)))) _ _) =
  let typs = map V.valueElemType vals
   in Just $ JsTestRun typs vals expect
mkRun _ = Nothing

instance Pretty JsTestRun where
  pretty (JsTestRun typs input expected) =
    "{" </> indent 2 (
      "inputTypes: ["
        <> commasep (map (\t -> "'" <> pretty (V.primTypeText t) <> "'") typs)
        <> "],"
      </> "input: " <> fmt input <> ","
      </> "expected: " <> fmt expected <> ","
    ) </> "}"
    where
      fmtVal :: V.PrimType -> V.Value -> Doc ann
      fmtVal V.I64 v = pretty v <> "n"
      fmtVal typ v = pretty v
      fmtArrRaw typ vs = "[" <> commasep (map (fmtVal typ) vs) <> "]"
      -- Hacky way to avoid the 'i32', 'i64' etc. suffixes as they are not valid
      -- JS.
      fixAnnots typ d = pretty $ T.replace (V.primTypeText typ) "" (prettyText d)
      fmtArray typ vs = fixAnnots typ $ fmtArrRaw typ vs
      fmt vss = "[" <> commasep (zipWith fmtArray typs vss) <> "]"

instance Pretty JsTestSpec where
  pretty (JsTestSpec entry runs) =
    "{" </> indent 2 (
      "entry: '" <> pretty entry <> "',"
      </> "runs: ["
      </> indent 2 (commastack $ map pretty runs)
      </> "],"
    ) </> "}"