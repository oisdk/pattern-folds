{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}

module PatternFolds (makePatternFolds,AsPatternFold(..)) where

import           PatternFolds.TH (makePatternFolds)

class AsPatternFold x f | x -> f where
  foldMatch :: (forall a. f r a -> a) -> (x -> r)
