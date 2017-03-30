# pattern-folds

Allows you to write code which pattern matches in a point-free way. Take the standard example of evaluating an expression tree:

```haskell
data Expr
  = Lit Integer
  | (:+) Expr Expr
  | (:*) Expr Expr

evalNormal :: Expr -> Integer
evalNormal (Lit x) = x
evalNormal (x :+ y) = evalNormal x + evalNormal y
evalNormal (x :* y) = evalNormal x * evalNormal y
```

With recusion schemes, some of the boilerplate can be removed:

```haskell
data Expr
  = Lit Integer
  | (:+) Expr Expr
  | (:*) Expr Expr

makeBaseFunctor ''Expr

evalRecScheme :: Expr -> Integer
evalRecScheme = cata alg where
  alg (LitF x) = x
  alg (x :+$ y) = x + y
  alg (x :*$ y) = x * y
```

`-XLambdaCase` can make this code terser still:

```haskell
data Expr
  = Lit Integer
  | (:+) Expr Expr
  | (:*) Expr Expr

makeBaseFunctor ''Expr

evalRecScheme :: Expr -> Integer
evalRecScheme = cata $ \case
  LitF x -> x
  x :+$ y -> x + y
  x :*$ y -> x * y
```

This module provides a template haskell function which will remove even more syntactic overhead, turning the above definition pointfree (when `-XRecordWildCards` is turned on):

```haskell
data Expr
  = Lit Integer
  | (:+) Expr Expr
  | (:*) Expr Expr

makeBaseFunctor ''Expr
makeHandler ''ExprF

evalRecScheme :: Expr -> Integer
evalRecScheme = cata (index ExprFAlg {..}) where
  litF = id
  (+$) = (+)
  (*$) = (*)
```

This handler structure is a representable functor, which is where the `index` function comes from.
