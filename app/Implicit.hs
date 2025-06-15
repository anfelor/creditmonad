{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ImpredicativeTypes #-}

-- | Testing the code about printing implicit queues.
module Implicit where

import Control.Monad.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Implicit

testImplicit :: Either String (Maybe (Int, String), Ticks)
testImplicit =
  runCounterM $ (=<<) (traverse (traverse showImplicit)) $
    empty >>= (`snoc` 1) >>= (`snoc` 2) >>= (`snoc` 3)
          >>= (`snoc` 4) >>= (`snoc` 5) >>= uncons