module Cats.CatsAsCategory

import Basic.Category
import Basic.Functor

public export
catsLeftIdentity :
     (cat1, cat2 : Category)
  -> (func : CFunctor cat1 cat2)
  -> functorComposition cat1 cat1 cat2 (idFunctor cat1) func = func
catsLeftIdentity cat1 cat2 func = functorEq
  cat1
  cat2
  (functorComposition cat1 cat1 cat2 (idFunctor cat1) func)
  func
  (\a => Refl)
  (\a, b, f => Refl)

public export
catsRightIdentity :
     (cat1, cat2 : Category)
  -> (func : CFunctor cat1 cat2)
  -> functorComposition cat1 cat2 cat2 func (idFunctor cat2) = func
catsRightIdentity cat1 cat2 func = functorEq
  cat1
  cat2
  (functorComposition cat1 cat2 cat2 func (idFunctor cat2))
  func
  (\a => Refl)
  (\a, b, f => Refl)

public export
catsAssociativity :
     (cat1, cat2, cat3, cat4 : Category)
  -> (func1 : CFunctor cat1 cat2)
  -> (func2 : CFunctor cat2 cat3)
  -> (func3 : CFunctor cat3 cat4)
  -> functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3)
   = functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3
catsAssociativity cat1 cat2 cat3 cat4 func1 func2 func3 = functorEq
   cat1
   cat4
   (functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3))
   (functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3)
   (\a => Refl)
   (\a, b, f => Refl)

public export
catsAsCategory : Category
catsAsCategory = MkCategory
  Category
  CFunctor
  idFunctor
  functorComposition
  catsLeftIdentity
  catsRightIdentity
  catsAssociativity