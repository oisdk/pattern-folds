{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DeriveFunctor         #-}

module RecordCase
  (makeHandler
  ,Handles(..)
  ,MaybeAlg(..)
  ,EitherAlg(..)
  ,ListAlg(..)
  ,FoldAlg(..))
  where

import RecordCase.TH (makeHandler)

-- | Allows matching on constructors to be applied partially. For instance:
--
-- > tail :: [a] -> [a]
-- > tail = recCase ListAlg {..} where
-- >   nil = []
-- >   cons = const id
class handler `Handles` patt  where
    recCase :: handler a -> patt -> a

makeHandler ''Maybe
makeHandler ''Either

data ListAlg a b = ListAlg
    { nil :: b
    , cons :: a -> [a] -> b
    } deriving Functor

instance (a ~ b) => ListAlg b `Handles` [a] where
    recCase r [] = nil r
    recCase r (x:xs) = cons r x xs
    {-# INLINE recCase  #-}

data FoldAlg a b = FoldAlg
    { func :: a -> b -> b
    , base :: b
    }

instance (a ~ b, Foldable f) =>
         FoldAlg a `Handles` f b where
    recCase (FoldAlg f b) = foldr f b
    {-# INLINE recCase #-}
