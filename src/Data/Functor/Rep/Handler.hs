{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module Data.Functor.Rep.Handler
  ( -- * Handlers
    makeHandler
  ,($|)

    -- * Example Handlers
  ,MaybeAlg(..)
  ,EitherAlg(..)
  ,BoolAlg(..)
    -- * Re-exports from Distributive and Representable
  ,Distributive(..)
  ,Representable(..)
  ,distributeRep)
  where

import           Data.Distributive (Distributive(..))
import           Data.Functor.Rep.Handler.TH     (makeHandler)
import           Data.Functor.Rep (Representable(..), distributeRep)

infixr 0 $|
-- | Apply a representable functor to its representation
($|) :: Representable handler => handler a -> Rep handler -> a
($|) = index
{-# INLINE ($|) #-}

makeHandler ''Maybe
makeHandler ''Either
makeHandler ''Bool
