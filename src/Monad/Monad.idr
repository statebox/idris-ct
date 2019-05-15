module Monad.Monad

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation

%access public export
%default total

record UnlawfulMonad (cat : Category) where
  constructor MkUnlawfulMonad
  functor : CFunctor cat cat
  unit : NaturalTransformation _ _ (idFunctor cat) functor
  multiplication : NaturalTransformation cat cat (functorComposition _ _ _ functor functor) functor
