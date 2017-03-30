{-# LANGUAGE FunctionalDependencies #-}

module RecordCase (makeRecordCase, AsRecordCase(..), recCase) where

import RecordCase.TH (makeRecordCase)

class AsRecordCase patt handler | patt -> handler where
  matchRecord :: patt -> handler a -> a

recCase :: AsRecordCase patt handler => handler a -> patt -> a
recCase = flip matchRecord
