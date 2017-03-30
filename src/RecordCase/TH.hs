module RecordCase.TH where

import Control.Lens hiding (cons)
import Language.Haskell.TH.Lens
import Language.Haskell.TH
import Control.Lens.Internal.TH
import Data.Monoid
import Data.Char
import Prelude
import Control.Monad (replicateM)

data NCon = NCon
  { _nconName :: Name
  , _nconForall :: [TyVarBndr]
  , _nconCxt  :: Maybe Cxt
  , _nconTypes :: [Type]
  }
  deriving (Eq)

instance HasTypeVars NCon where
  typeVarsEx s f (NCon x w y  z) = NCon x w <$> typeVarsEx s f y <*> typeVarsEx s f z

nconName :: Lens' NCon Name
nconName f x = fmap (\y -> x {_nconName = y}) (f (_nconName x))

nconCxt :: Lens' NCon (Maybe Cxt)
nconCxt f x = fmap (\y -> x {_nconCxt = y}) (f (_nconCxt x))

nconTypes :: Lens' NCon [Type]
nconTypes f x = fmap (\y -> x {_nconTypes = y}) (f (_nconTypes x))

makeHandler :: Name -> DecsQ
makeHandler typeName = do
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
normalizeCon (RecC    conName xs) = [NCon conName [] Nothing (map (view _3) xs)]
normalizeCon (NormalC conName xs) = [NCon conName [] Nothing (map (view _2) xs)]
normalizeCon (InfixC (_,x) conName (_,y)) = [NCon conName [] Nothing [x,y]]
normalizeCon (ForallC [] [] con) = normalizeCon con -- happens in GADTs
normalizeCon (ForallC o cx1 con) =
  [NCon n (o++w) (Just cx1 <> cx2) tys
     | NCon n w cx2 tys <- normalizeCon con ]
normalizeCon (GadtC conNames xs _)    =
  [ NCon conName [] Nothing (map (view _2) xs) | conName <- conNames ]
normalizeCon (RecGadtC conNames xs _) =
  [ NCon conName [] Nothing (map (view _3) xs) | conName <- conNames ]

makeConsFolds :: Name -> [TyVarBndr] -> [NCon] -> DecsQ
makeConsFolds nm ty cons = do
    newTyName <- pure (foldGadtName nm)
    let monInst = do
            lhs <- newName "x"
            rhs <- newName "f"
            InstanceD Nothing [] (AppT (ConT (mkName "Monad")) newTypeLifted') <$>
                sequence
                    [ FunD (mkName ">>=") <$>
                      sequence
                          [ Clause [VarP lhs, VarP rhs] <$>
                            (NormalB <$> bind lhs rhs) <*>
                            pure []]
                    , pragInlD (mkName ">>=") Inline FunLike AllPhases
                    ]
        bind lhs rhs =
            foldl AppE (ConE newTyName) <$> traverse (bind' lhs rhs) cons
        bind' lhs rhs cn =
            case length (cn ^. nconTypes) of
                0 ->
                    pure $
                    foldr1
                        AppE
                        [ VarE (foldConsName (cn ^. nconName))
                        , VarE rhs
                        , VarE (foldConsName (cn ^. nconName))
                        , VarE lhs]
                _ -> do
                    vars <- traverse (const (newName "x")) (cn ^. nconTypes)
                    let appp l =
                            foldl
                                AppE
                                (VarE (foldConsName (cn ^. nconName)))
                                (l : map VarE vars)
                    pure $
                        LamE
                            (map VarP vars)
                            (appp (AppE (VarE rhs) (appp (VarE lhs))))
        go = do
            rn <- newName "r"
            let r = PlainTV rn
            case cons of
                [x] ->
                    NewtypeD [] newTyName (ty ++ [r]) Nothing <$>
                    (RecC newTyName <$> traverse (h (VarT rn)) [x]) <*>
                    pure [ConT (mkName "Functor")]
                _ ->
                    DataD [] newTyName (ty ++ [r]) Nothing <$>
                    (pure . RecC newTyName <$> traverse (h (VarT rn)) cons) <*>
                    pure [ConT (mkName "Functor")]
        h r ncon =
            return
                ( foldConsName (ncon ^. nconName)
                , Bang NoSourceUnpackedness NoSourceStrictness
                , let fnt = funcType (ncon ^. nconTypes) r
                  in maybe
                         fnt
                         (\c ->
                               ForallT (_nconForall ncon) c fnt)
                         (ncon ^. nconCxt))
        funcType ts r =
            foldr
                (\x xs ->
                      AppT (AppT ArrowT x) xs)
                r
                ts
        origType = foldl AppT (ConT nm) (convertTVBs ty)
        newTypeLifted xs = foldl AppT (ConT newTyName) (map VarT xs)
        newTypeLifted' = foldl AppT (ConT newTyName) (convertTVBs ty)
        rest =
            InstanceD
                Nothing
                []
                (AppT (ConT (mkName "Representable")) newTypeLifted') <$>
            sequence
                [ pure $
                  TySynInstD
                      (mkName "Rep")
                      (TySynEqn [newTypeLifted'] origType)
                , FunD (mkName "index") . (: []) <$> instanceFunc
                , pragInlD (mkName "index") Inline FunLike AllPhases
                , FunD (mkName "tabulate") . (: []) <$> mkHandlerFunc
                , pragInlD (mkName "tabulate") Inline FunLike AllPhases]
        distInst =
            pure $
            InstanceD
                Nothing
                []
                (AppT (ConT (mkName "Distributive")) newTypeLifted')
                [ FunD
                      (mkName "distribute")
                      [Clause [] (NormalB (VarE (mkName "distributeRep"))) []]]
        mkHandlerFunc = do
            alg <- newName "alg"
            Clause [VarP alg] <$>
                (NormalB . foldl AppE (ConE newTyName) <$>
                 traverse (gi alg) cons) <*>
                pure []
        gi alg cn = do
            vars <- traverse (const (newName "x")) (cn ^. nconTypes)
            pure $
                case vars of
                    [] -> AppE (VarE alg) (ConE (cn ^. nconName))
                    _ ->
                        LamE
                            (map VarP vars)
                            (AppE
                                 (VarE alg)
                                 (foldl
                                      AppE
                                      (ConE (cn ^. nconName))
                                      (map VarE vars)))
        instanceFunc = do
            expr <- newName "x"
            alg <- newName "handler"
            Clause [VarP alg, VarP expr] <$>
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
                    []
        appInst = do
            pnm <- newName "x"
            lhs <- traverse (const (newName "fs")) cons
            rhs <- traverse (const (newName "xs")) cons
            InstanceD
                Nothing
                []
                (AppT
                     (ConT (mkName "Applicative"))
                     (newTypeLifted (map bndrName ty))) <$>
                sequence
                    [ pure $
                      FunD
                          (mkName "pure")
                          [ Clause
                                [VarP pnm]
                                (NormalB
                                     (foldl
                                          AppE
                                          (ConE newTyName)
                                          (map (rep' pnm) cons)))
                                []]
                    , pragInlD (mkName "pure") Inline FunLike AllPhases
                    , FunD (mkName "<*>") <$>
                      sequence
                          [ Clause
                                [ ConP newTyName (map VarP lhs)
                                , ConP newTyName (map VarP rhs)] <$>
                            (NormalB <$>
                             (foldl AppE (ConE newTyName) <$>
                              sequence (zipWith3 app' lhs rhs cons))) <*>
                            pure []]
                    , pragInlD (mkName "<*>") Inline FunLike AllPhases
                    , pure $
                      FunD
                          (mkName "<*")
                          [Clause [] (NormalB (VarE (mkName "const"))) []]
                    , pure $
                      FunD
                          (mkName "*>")
                          [ Clause
                                []
                                (NormalB
                                     (AppE
                                          (VarE (mkName "const"))
                                          (VarE (mkName "id"))))
                                []]
                    , pragInlD (mkName "<*") Inline FunLike AllPhases
                    , pragInlD (mkName "*>") Inline FunLike AllPhases]
        rep' pnm cns =
            case length (cns ^. nconTypes) of
                0 -> VarE pnm
                n -> LamE (replicate n WildP) (VarE pnm)
        app' f x c =
            case length (c ^. nconTypes) of
                0 -> pure (AppE (VarE f) (VarE x))
                n -> do
                    vars <- replicateM n (newName "y")
                    pure $
                        LamE
                            (map VarP vars)
                            (AppE
                                 (foldl AppE (VarE f) (map VarE vars))
                                 (foldl AppE (VarE x) (map VarE vars)))
    sequenceA [go, rest, appInst, distInst, monInst]

foldGadtName :: Name -> Name
foldGadtName n = case nameBase n of
  [] -> error "foldGadtName: empty name base?"
  x:xs | isUpper x -> mkName (x : xs ++ "Alg")
       | otherwise -> mkName (x : xs ++ "|")

foldConsName :: Name -> Name
foldConsName n = case nameBase n of
  [] -> error "foldGadtName: empty name base?"
  x:xs | isUpper x -> mkName (toLower x : xs)
       | otherwise -> mkName xs

convertTVBs :: [TyVarBndr] -> [Type]
convertTVBs = map (VarT . bndrName)
