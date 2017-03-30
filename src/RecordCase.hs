{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module RecordCase
  (MaybeAlg(..)
  ,EitherAlg(..)
  ,BoolAlg(..)
  ,($|))
  where

import           Data.Distributive
import           RecordCase.TH     (makeHandler)

import           Data.Functor.Rep

infixr 0 $|
($|) :: Representable handler => handler a -> Rep handler -> a
($|) = index
{-# INLINE ($|) #-}

makeHandler ''Maybe
makeHandler ''Either
makeHandler ''Bool
