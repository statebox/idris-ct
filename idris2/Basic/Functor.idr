module Basic.Functor

import Basic.Category

public export
record CFunctor (cat1 : Category) (cat2 : Category) where
  constructor MkCFunctor
  mapObj          : obj cat1 -> obj cat2
  mapMor          : (a, b : obj cat1)
                 -> mor cat1 a b
                 -> mor cat2 (mapObj a) (mapObj b)
  preserveId      : (a : obj cat1)
                 -> mapMor a a (identity cat1 a) = identity cat2 (mapObj a)
  preserveCompose : (a, b, c : obj cat1)
                 -> (f : mor cat1 a b)
                 -> (g : mor cat1 b c)
                 -> mapMor a c (compose cat1 a b c f g)
                  = compose cat2 (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)

public export
functorEq : (cat1, cat2 : Category)
  -> (fun1, fun2 : CFunctor cat1 cat2)
  -> ((a : obj cat1) -> mapObj fun1 a = mapObj fun2 a)
  -> ((a, b : obj cat1) -> (f : mor cat1 a b) -> mapMor fun1 a b f ~=~ mapMor fun2 a b f)
  -> fun1 = fun2
functorEq cat1 cat2 fun1 fun2 prfObj prfMor = believe_me ()

public export
idFunctor : (cat : Category) -> CFunctor cat cat
idFunctor cat = MkCFunctor
  id
  (\a, b => id)
  (\a => Refl)
  (\a, b, c, f, g => Refl)

public export
functorComposition :
     (cat1, cat2, cat3 : Category)
  -> CFunctor cat1 cat2
  -> CFunctor cat2 cat3
  -> CFunctor cat1 cat3
functorComposition cat1 cat2 cat3 fun1 fun2 = MkCFunctor
  ((mapObj fun2) . (mapObj fun1))
  (\a, b => (mapMor fun2 (mapObj fun1 a) (mapObj fun1 b)) . (mapMor fun1 a b))
  (\a => trans (cong (mapMor fun2 (mapObj fun1 a) (mapObj fun1 a)) (preserveId fun1 a))
               (preserveId fun2 (mapObj fun1 a))
  )
  (\a, b, c, f, g => trans (cong (mapMor fun2 (mapObj fun1 a) (mapObj fun1 c)) (preserveCompose fun1 a b c f g))
                           (preserveCompose fun2
                                            (mapObj fun1 a)
                                            (mapObj fun1 b)
                                            (mapObj fun1 c)
                                            (mapMor fun1 a b f)
                                            (mapMor fun1 b c g)))
