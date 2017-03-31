module Data.Functor.Rep.Handler.TH where

import Language.Haskell.TH
import Data.Monoid
import Data.Char
import Prelude
import Control.Monad (replicateM)

data NCon = NCon
  { _nConName :: Name
  , _nConForall :: [TyVarBndr]
  , _nConCxt  :: Maybe Cxt
  , _nConTypes :: [Type]
  }
  deriving (Eq)

numTypes :: NCon -> Int
numTypes = length . _nConTypes

-- | This function will create a "handler" structure for a given ADT.
-- For instance, given a datatype like so:
--
-- @
-- data Expr
--   = Lit Integer
--   | (:+:) Expr Expr
--   | (:*:) Expr Expr
--
-- makeHandler ''Expr
-- @
--
-- The following "handler" will be created:
--
-- @
-- data ExprAlg a
--   = ExprAlg
--   { lit :: Integer -> a
--   , (+:) :: Expr -> Expr -> a
--   , (*:) :: Expr -> Expr -> a
--   } deriving Functor
-- @
--
-- This type is an algebra for @Expr@: it can turn a value of @Expr@ into
-- a value of @a@. The function which applies a handler to the structure
-- it handles is 'Data.Functor.Rep.index', from the
-- 'Data.Functor.Rep.Representable' class:
--
-- @
-- eval :: Expr -> Integer
-- eval = 'Data.Functor.Rep.index' evalAlg where
--   evalAlg
--     = ExprAlg
--         id
--         (\x y -> eval x + eval y)
--         (\x y -> eval x * eval y)
-- @
--
-- There are a number of uses for this "handler" type. One is that it can
-- be used to emulate pointfree pattern matching with the record wildcards
-- extension:
--
-- @
-- eval :: Expr -> Integer
-- eval = 'Data.Functor.Rep.index' ExprAlg {..} where
--   lit x = x
--   (+:) = 'Data.Function.on' (+) eval
--   (*:) = 'Data.Function.on' (*) eval
-- @
--
-- In combination with the
-- <https://hackage.haskell.org/package/recursion-schemes recursion-schemes>
-- package, you can remove almost all redundancy from the above function:
--
-- @
-- makeBaseFunctor ''Expr
-- makeHandler ''ExprF
--
-- eval :: Expr -> Integer
-- eval = cata (index ExprFAlg {..}) where
--   litF = id
--   (+:$) = (+)
--   (*:$) = (*)
-- @
--
-- The handlers are all instances of 'Functor', 'Applicative', and 'Monad'
-- (they're isomorphic to reader), allowing them to be combined using the
-- standard combinators. They're also instances of
-- 'Data.Distributive.Distributive' and 'Data.Functor.Rep.Representable'.
-- Each handler is a representable functor, where its representation is the
-- type it handles.
--
-- The generation function will try to handle GADTs properly, with any odd
-- constraints on the types they contain:
--
-- @
-- data Difficult a b c where
--   Existential :: forall a b c d. Show d => d -> Difficult a b c
--   Constrained :: (Eq b, Ord c) => Difficult a b c
--
-- makeHandler ''Difficult
-- @
--
-- Will create:
--
-- @
-- data DifficultAlg a b c r
--   = DifficultAlg
--   { existential :: forall d. Show d => d -> r
--   , constrained :: (Eq b, Ord c) => r
--   } deriving Functor
-- @

makeHandler :: Name -> DecsQ
makeHandler typeName = do
  info <- reify typeName
  case info of
    TyConI dec -> makeDecHandler dec
    _          -> fail "makeHandler: expected type constructor name"

makeDecHandler :: Dec -> DecsQ
makeDecHandler dec = case dec of
  DataD        _ ty vars _ cons _ -> next ty vars cons
  NewtypeD     _ ty vars _ con  _ -> next ty vars [con]
  _                               -> fail "makeDecHandler: expected type constructor dec"
  where
  next ty args cons =
    makeConsHandler ty args (concatMap normalizeCon cons)

normalizeCon :: Con -> [NCon]
normalizeCon (RecC    conName xs) = [NCon conName [] Nothing (map (\(_,_,z) -> z) xs)]
normalizeCon (NormalC conName xs) = [NCon conName [] Nothing (map snd xs)]
normalizeCon (InfixC (_,x) conName (_,y)) = [NCon conName [] Nothing [x,y]]
normalizeCon (ForallC [] [] con) = normalizeCon con -- happens in GADTs
normalizeCon (ForallC o cx1 con) =
  [NCon n (o++w) (Just cx1 <> cx2) tys
     | NCon n w cx2 tys <- normalizeCon con ]
normalizeCon (GadtC conNames xs _)    =
  [ NCon conName [] Nothing (map snd xs) | conName <- conNames ]
normalizeCon (RecGadtC conNames xs _) =
  [ NCon conName [] Nothing (map (\(_,_,z) -> z) xs) | conName <- conNames ]

inline :: String -> DecQ
inline nme = pragInlD (mkName nme) Inline FunLike AllPhases

applyFunc :: Exp -> [Exp] -> Exp
applyFunc = foldl AppE

funcType :: [Type] -> Type -> Type
funcType ts r =
    foldr
        (\x xs ->
              AppT (AppT ArrowT x) xs)
        r
        ts

const' :: Name -> NCon -> Exp
const' pnm cns =
        case numTypes cns of
            0 -> VarE pnm
            n -> LamE (replicate n WildP) (VarE pnm)

app' :: Name -> Name -> NCon -> Q Exp
app' f x c =
      case numTypes c of
          0 -> pure (VarE f |$| VarE x)
          n -> do
              vars <- replicateM n (newName "y")
              pure $
                  LamE
                      (map VarP vars)
                      (applyFunc (VarE f) (map VarE vars) |$| applyFunc (VarE x) (map VarE vars))


inst :: Type -> String -> [Dec] -> Dec
inst instanceType className =
    InstanceD Nothing [] (AppT (ConT (mkName className)) instanceType)

monInst :: Name -> Type -> [NCon] -> Q Dec
monInst handlerTyName newTy cons = do
    lhs <- newName "x"
    rhs <- newName "f"
    let bindField cn =
            case numTypes cn of
                0 ->
                    pure $ VarE fieldName
                        |$ VarE rhs
                        |$ VarE fieldName
                        |$ VarE lhs
                _ -> do
                    vars <- replicateM (numTypes cn) (newName "x")
                    let runInner l =
                            applyFunc
                                (VarE fieldName)
                                (l : map VarE vars)
                    pure $
                        LamE
                            (map VarP vars)
                            (runInner (VarE rhs |$| runInner (VarE lhs)))
              where fieldName = toHandlerFieldName (_nConName cn)
    fields <- traverse bindField cons
    inliner <- inline ">>="
    pure $
        inst newTy
            "Monad"
            [ FunD
                  (mkName ">>=")
                  [ Clause
                        [VarP lhs, VarP rhs]
                        (NormalB (applyFunc (ConE handlerTyName) fields))
                        []]
            , inliner]

handlerDecl :: Name -> [NCon] -> [TyVarBndr] -> Q Dec
handlerDecl handlerTyName cons ty = do
    rn <- newName "r"
    let r = PlainTV rn
    let handlerField ncon =
            ( toHandlerFieldName (_nConName ncon)
            , Bang NoSourceUnpackedness NoSourceStrictness
            , let fnt = funcType (_nConTypes ncon) (VarT rn)
              in maybe
                     fnt
                     (\c ->
                           ForallT (_nConForall ncon) c fnt)
                     (_nConCxt ncon))
    pure $
        case cons of
            [x] ->
                NewtypeD
                    []
                    handlerTyName
                    (ty ++ [r])
                    Nothing
                    (RecC handlerTyName [handlerField x])
                    [ConT (mkName "Functor")]
            _ ->
                DataD
                    []
                    handlerTyName
                    (ty ++ [r])
                    Nothing
                    [RecC handlerTyName (map handlerField cons)]
                    [ConT (mkName "Functor")]

repInst :: Name -> Type -> Type -> [NCon] -> Q Dec
repInst handlerTyName handlerType origType cons =
    inst handlerType "Representable" <$>
    sequence
        [ pure $
          TySynInstD (mkName "Rep") (TySynEqn [handlerType] origType)
        , FunD (mkName "index") <$> sequence [indexFunc]
        , inline "index"
        , FunD (mkName "tabulate") <$> sequence [tabulateFunc]
        , inline "tabulate"]
  where
    tabulateFunc = do
        alg <- newName "alg"
        let tabulateField cn = do
                vars <- replicateM (numTypes cn) (newName "x")
                pure $
                    case vars of
                        [] -> VarE alg |$| ConE (_nConName cn)
                        _ ->
                            LamE
                                (map VarP vars)
                                (AppE
                                      (VarE alg)
                                      (applyFunc
                                          (ConE (_nConName cn))
                                          (map VarE vars)))
        fields <- traverse tabulateField cons
        pure $
            Clause
                [VarP alg]
                (NormalB (applyFunc (ConE handlerTyName) fields))
                []
    indexFunc = do
        alg <- newName "handler"
        let indexField cn = do
                vars <- replicateM (numTypes cn) (newName "x")
                pure $
                    Match
                        (ConP (_nConName cn) (map VarP vars))
                        (NormalB
                              (applyFunc
                                  (VarE
                                        (toHandlerFieldName (_nConName cn)))
                                  (map VarE (alg : vars))))
                        []
        expr <- newName "x"
        fields <- traverse indexField cons
        pure $
            Clause
                [VarP alg, VarP expr]
                (NormalB (CaseE (VarE expr) fields))
                []

distInst :: Type -> Q Dec
distInst handlerType =
    inst handlerType "Distributive" .
    flip
        (:)
        [ FunD
              (mkName "distribute")
              [Clause [] (NormalB (VarE (mkName "distributeRep"))) []]] <$>
    inline "distribute"

appInst :: Name -> Type -> [NCon] -> Q Dec
appInst handlerTyName handlerType cons = do
    pnm <- newName "x"
    lhs <- replicateM (length cons) (newName "fs")
    rhs <- replicateM (length cons) (newName "xs")
    let pure' =
            FunD
                (mkName "pure")
                [ Clause
                      [VarP pnm]
                      (NormalB
                           (applyFunc
                                (ConE handlerTyName)
                                (map (const' pnm) cons)))
                      []]
    liftAppFnc <- sequence (zipWith3 app' lhs rhs cons)
    let appD =
            FunD
                (mkName "<*>")
                [ Clause
                      [ ConP handlerTyName (map VarP lhs)
                      , ConP handlerTyName (map VarP rhs)]
                      (NormalB (applyFunc (ConE handlerTyName) liftAppFnc))
                      []]
    inst handlerType "Applicative" <$>
        sequence
            [ pure pure'
            , inline "pure"
            , pure appD
            , inline "<*>"
            , pure $
              FunD
                  (mkName "<*")
                  [Clause [] (NormalB (VarE (mkName "const"))) []]
            , inline "<*"
            , pure $
              FunD
                  (mkName "*>")
                  [ Clause
                        []
                        (NormalB (VarE (mkName "const") |$| VarE (mkName "id")))
                        []]
            , inline "*>"]

makeConsHandler :: Name -> [TyVarBndr] -> [NCon] -> DecsQ
makeConsHandler nm ty cons =
    sequence
        [ handlerDecl handlerTyName cons ty
        , repInst handlerTyName handlerType origType cons
        , appInst handlerTyName handlerType cons
        , distInst handlerType
        , monInst handlerTyName handlerType cons]
  where
    handlerTyName = toHandlerTypeName nm
    origType = foldl AppT (ConT nm) (convertTVBs ty)
    handlerType = foldl AppT (ConT handlerTyName) (convertTVBs ty)

toHandlerTypeName :: Name -> Name
toHandlerTypeName =
    mkName . toHandlerTypeName' . nameBase
  where
    toHandlerTypeName' [] = error "toHandlerTypeName: empty name base?"
    toHandlerTypeName' (x:xs)
      | isUpper x = x : xs ++ "Alg"
      | otherwise = x : xs ++ "|"

toHandlerFieldName :: Name -> Name
toHandlerFieldName =
    mkName .
    toHandlerFieldName' . nameBase
  where
    toHandlerFieldName' [] = error "toHandlerFieldName: empty name base?"
    toHandlerFieldName' (':':xs) = xs
    toHandlerFieldName' (x:xs) = toLower x : xs

convertTVBs :: [TyVarBndr] -> [Type]
convertTVBs = map (VarT . bndrName) where
  bndrName (PlainTV n) = n
  bndrName (KindedTV n _) = n

infixl 1 |$|
(|$|) :: Exp -> Exp -> Exp
(|$|) = AppE

infixr 1 |$
(|$) :: Exp -> Exp -> Exp
(|$) = AppE
