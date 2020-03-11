module Cats.FunctorsAsCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalTransformation

public export
functorCategory : (cat1, cat2 : Category) -> Category
functorCategory cat1 cat2 = MkCategory
  (CFunctor cat1 cat2)
  (NaturalTransformation cat1 cat2)
  (idTransformation cat1 cat2)
  (naturalTransformationComposition cat1 cat2)
  (\fun1, fun2, n =>
    naturalTransformationExt cat1 cat2 fun1 fun2 _
      n
      (\a => (leftIdentity _ _ _ _)))
  (\fun1, fun2, n =>
    naturalTransformationExt cat1 cat2 fun1 fun2 _
      n
      (\a => (rightIdentity _ _ _ _)))
  (\fun1, fun2, fun3, fun4,
    (MkNaturalTransformation comp1 comm1),
    (MkNaturalTransformation comp2 comm2),
    (MkNaturalTransformation comp3 comm3) =>
      naturalTransformationExt cat1 cat2 fun1 fun4 _ _
      (\a => associativity _ _ _ _ _ _ _ _))
