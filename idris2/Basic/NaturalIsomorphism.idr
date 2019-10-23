module Basic.NaturalIsomorphism

import Basic.Category
import Basic.Functor
import Basic.Isomorphism
import Basic.NaturalTransformation

public export
record NaturalIsomorphism
  (cat1 : Category)
  (cat2 : Category)
  (fun1 : CFunctor cat1 cat2)
  (fun2 : CFunctor cat1 cat2)
where
  constructor MkNaturalIsomorphism
  natTrans : NaturalTransformation cat1 cat2 fun1 fun2
  isIso    : (a : obj cat1) -> Isomorphism cat2 (mapObj fun1 a) (mapObj fun2 a) (component natTrans a)
