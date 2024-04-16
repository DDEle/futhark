{-# LANGUAGE TemplateHaskell #-}

-- | Code snippets used by the JS backends.
module Futhark.CodeGen.RTS.JavaScript
  ( serverJs,
    serverBrowserJs,
    valuesJs,
    wrapperclassesJs,
  )
where

import Data.FileEmbed
import Data.Text qualified as T

-- | @rts/javascript/server.js@
serverJs :: T.Text
serverJs = $(embedStringFile "rts/javascript/server.js")

-- | @rts/javascript/server_browser.js@
serverBrowserJs :: T.Text
serverBrowserJs = $(embedStringFile "rts/javascript/server_browser.js")
{-# NOINLINE serverBrowserJs #-}

-- | @rts/javascript/values.js@
valuesJs :: T.Text
valuesJs = $(embedStringFile "rts/javascript/values.js")

-- | @rts/javascript/wrapperclasses.js@
wrapperclassesJs :: T.Text
wrapperclassesJs = $(embedStringFile "rts/javascript/wrapperclasses.js")
