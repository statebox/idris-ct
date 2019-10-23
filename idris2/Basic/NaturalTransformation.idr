module Basic.NaturalTransformation

import Basic.Category
import Basic.Functor

public export
record NaturalTransformation
  (cat1 : Category)
  (cat2 : Category)
  (fun1 : CFunctor cat1 cat2)
  (fun2 : CFunctor cat1 cat2)
  where
    constructor MkNaturalTransformation
    component : (a : obj cat1) -> mor cat2 (mapObj fun1 a) (mapObj fun2 a)
    commutativity : (a, b : obj cat1)
                 -> (f : mor cat1 a b)
                 -> compose cat2
                            (mapObj fun1 a)
                            (mapObj fun2 a)
                            (mapObj fun2 b)
                            (component a)
                            (mapMor fun2 a b f)
                  = compose cat2
                            (mapObj fun1 a)
                            (mapObj fun1 b)
                            (mapObj fun2 b)
                            (mapMor fun1 a b f)
                            (component b)
