module RecordCase.TH where

import Control.Lens hiding (cons)
import Language.Haskell.TH.Lens
import Language.Haskell.TH
import Control.Lens.Internal.TH
import Data.Monoid
import Data.Char
import Prelude

data NCon = NCon
  { _nconName :: Name
  , _nconCxt  :: Maybe Cxt
  , _nconTypes :: [Type]
  }
  deriving (Eq)

instance HasTypeVars NCon where
  typeVarsEx s f (NCon x y z) = NCon x <$> typeVarsEx s f y <*> typeVarsEx s f z

nconName :: Lens' NCon Name
nconName f x = fmap (\y -> x {_nconName = y}) (f (_nconName x))

nconCxt :: Lens' NCon (Maybe Cxt)
nconCxt f x = fmap (\y -> x {_nconCxt = y}) (f (_nconCxt x))

nconTypes :: Lens' NCon [Type]
nconTypes f x = fmap (\y -> x {_nconTypes = y}) (f (_nconTypes x))

makeRecordCase :: Name -> DecsQ
makeRecordCase typeName = do
  info <- reify typeName
  case info of
    TyConI dec -> makeDecFolds dec
    _          -> fail "makeRecordCase: expected type constructor name"

makeDecFolds :: Dec -> DecsQ
makeDecFolds dec = case dec of
  DataD        _ ty vars _ cons _ -> next ty vars cons
  NewtypeD     _ ty vars _ con  _ -> next ty vars [con]
  _                             -> fail "makeRecordCase: expected type constructor dec"
  where

  next ty args cons =
    makeConsFolds ty args (concatMap normalizeCon cons)

normalizeCon :: Con -> [NCon]
normalizeCon (RecC    conName xs) = [NCon conName Nothing (map (view _3) xs)]
normalizeCon (NormalC conName xs) = [NCon conName Nothing (map (view _2) xs)]
normalizeCon (InfixC (_,x) conName (_,y)) = [NCon conName Nothing [x,y]]
normalizeCon (ForallC [] [] con) = normalizeCon con -- happens in GADTs
normalizeCon (ForallC _ cx1 con) =
  [NCon n (Just cx1 <> cx2) tys
     | NCon n cx2 tys <- normalizeCon con ]
normalizeCon (GadtC conNames xs _)    =
  [ NCon conName Nothing (map (view _2) xs) | conName <- conNames ]
normalizeCon (RecGadtC conNames xs _) =
  [ NCon conName Nothing (map (view _3) xs) | conName <- conNames ]

makeConsFolds :: Name -> [TyVarBndr] -> [NCon] -> DecsQ
makeConsFolds nm ty cons = sequenceA [go, rest]
  where
    go = do
        rn <- newName "r"
        let r = PlainTV rn
        DataD [] (foldGadtName nm) (ty ++ [r]) Nothing <$>
            (pure . RecC (foldGadtName nm) <$> traverse (h (VarT rn)) cons) <*>
            pure []
    h r ncon =
        return
            ( foldConsName (ncon ^. nconName)
            , Bang NoSourceUnpackedness NoSourceStrictness
            , funcType (ncon ^. nconTypes) r)
    funcType ts r =
        foldr
            (\x xs ->
                  AppT (AppT ArrowT x) xs)
            r
            ts
    origType = foldl AppT (ConT nm) (convertTVBs ty)
    newTypeLifted = foldl AppT (ConT (foldGadtName nm)) (convertTVBs ty)
    rest =
        InstanceD
            Nothing
            []
            (foldl
                 AppT
                 (ConT (mkName "AsRecordCase"))
                 [origType, newTypeLifted]) <$>
        sequence [FunD (mkName "matchRecord") . (: []) <$> instanceFunc]
    instanceFunc = do
        expr <- newName "x"
        alg <- newName "handler"
        Clause [VarP expr, VarP alg] <$>
            (NormalB <$> (CaseE (VarE expr) <$> traverse (run alg) cons)) <*>
            pure []
    run fnc cn = do
        vars <- traverse (const (newName "x")) (cn ^. nconTypes)
        pure $
            Match
                (ConP (cn ^. nconName) (map VarP vars))
                (NormalB
                     (foldl
                          AppE
                          (VarE (foldConsName (cn ^. nconName)))
                          (map VarE (fnc : vars))))
                []-- Match 

foldGadtName :: Name -> Name
foldGadtName n = case nameBase n of
  [] -> error "foldGadtName: empty name base?"
  x:xs | isUpper x -> mkName (x : xs ++ "Alg")
       | otherwise -> mkName (x : repC xs)
       where
         repC [] = "|"
         repC ":" = "|"
         repC (c:cs) = c : repC cs

foldConsName :: Name -> Name
foldConsName n = case nameBase n of
  [] -> error "foldGadtName: empty name base?"
  x:xs | isUpper x -> mkName (toLower x : xs)
       | otherwise -> mkName (xs ++ ":")

convertTVBs :: [TyVarBndr] -> [Type]
convertTVBs = map (VarT . bndrName)
