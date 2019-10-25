module Cats.FunctorsAsCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation

public export
idTransformation :
     (cat1, cat2 : Category)
  -> (fun : CFunctor cat1 cat2)
  -> NaturalTransformation cat1 cat2 fun fun
idTransformation cat1 cat2 fun = MkNaturalTransformation
  (\a => identity cat2 (mapObj fun a))
  (\a, b, f => trans (leftIdentity cat2 _ _ (mapMor fun a b f))
                     (sym $ rightIdentity cat2 _ _ (mapMor fun a b f)))

public export
functorCategory : (cat1, cat2 : Category) -> Category
functorCategory cat1 cat2 = MkCategory
  (CFunctor cat1 cat2)
  (NaturalTransformation cat1 cat2)
  (idTransformation cat1 cat2)
  (naturalTransformationComposition cat1 cat2)
  (\fun1, fun2, nt =>
    naturalTransformationExt cat1 cat2 fun1 fun2 _
      nt
      (\a => (leftIdentity _ _ _ _)))
  (\fun1, fun2, nt =>
    naturalTransformationExt cat1 cat2 fun1 fun2 _
      nt
      (\a => (rightIdentity _ _ _ _)))
  (\fun1, fun2, fun3, fun4, nt1, nt2, nt3 =>
    naturalTransformationExt cat1 cat2 fun1 fun4 _ _
    (\a => associativity _ _ _ _ _ _ _ _))
