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
naturalTransformationExt :
     (cat1, cat2 : Category)
  -> (fun1, fun2 : CFunctor cat1 cat2)
  -> (trans1, trans2 : NaturalTransformation cat1 cat2 fun1 fun2)
  -> ((a : obj cat1) -> component trans1 a = component trans2 a)
  -> trans1 = trans2
naturalTransformationExt _ _ _ _ _ _ _ = believe_me ()

public export
naturalTransformationComposition :
     (cat1, cat2 : Category)
  -> (fun1, fun2, fun3 : CFunctor cat1 cat2)
  -> NaturalTransformation cat1 cat2 fun1 fun2
  -> NaturalTransformation cat1 cat2 fun2 fun3
  -> NaturalTransformation cat1 cat2 fun1 fun3
naturalTransformationComposition cat1 cat2 fun1 fun2 fun3 natTrans1 natTrans2 =
    MkNaturalTransformation
      (\a => compose cat2 (mapObj fun1 a)
                          (mapObj fun2 a)
                          (mapObj fun3 a)
                          (component natTrans1 a)
                          (component natTrans2 a))
      (\a, b, f =>
        trans
          (sym $ associativity cat2 _ _ _ _ (component natTrans1 a) (component natTrans2 a) (mapMor fun3 a b f))
        (trans (cong (compose cat2 (mapObj fun1 a) (mapObj fun2 a) (mapObj fun3 b) (component natTrans1 a))
                     (commutativity natTrans2 a b f))
        (trans (associativity cat2 _ _ _ _ (component natTrans1 a) (mapMor fun2 a b f) (component natTrans2 b))
        (trans (cong (\x => compose cat2 _ _ _ x (component natTrans2 b))
                     (commutativity natTrans1 a b f))
        (sym $ associativity cat2 _ _ _ _ (mapMor fun1 a b f) (component natTrans1 b) (component natTrans2 b))))))

public export
composeFunctorNatTrans :
     {cat1, cat2, cat3 : Category}
  -> {fun1, fun2 : CFunctor cat1 cat2}
  -> NaturalTransformation cat1 cat2 fun1 fun2
  -> (fun3 : CFunctor cat2 cat3)
  -> NaturalTransformation cat1 cat3
     (functorComposition cat1 cat2 cat3 fun1 fun3)
     (functorComposition cat1 cat2 cat3 fun2 fun3)
composeFunctorNatTrans {cat3} {fun1} {fun2} natTrans fun3 = MkNaturalTransformation
  (\a => mapMor fun3 (mapObj fun1 a) (mapObj fun2 a) (component natTrans a))
  (\a, b, f => trans (sym $ preserveCompose fun3
                                            (mapObj fun1 a)
                                            (mapObj fun2 a)
                                            (mapObj fun2 b)
                                            (component natTrans a)
                                            (mapMor fun2 a b f))
               (trans (cong (mapMor fun3 (mapObj fun1 a) (mapObj fun2 b)) (commutativity natTrans a b f))
                      (preserveCompose fun3
                                       (mapObj fun1 a)
                                       (mapObj fun1 b)
                                       (mapObj fun2 b)
                                       (mapMor fun1 a b f)
                                       (component natTrans b))))

public export
composeNatTransFunctor :
     {cat1, cat2, cat3 : Category}
  -> {fun2, fun3 : CFunctor cat2 cat3}
  -> (fun1 : CFunctor cat1 cat2)
  -> NaturalTransformation cat2 cat3 fun2 fun3
  -> NaturalTransformation cat1 cat3
    (functorComposition cat1 cat2 cat3 fun1 fun2)
    (functorComposition cat1 cat2 cat3 fun1 fun3)
composeNatTransFunctor fun1 natTrans = MkNaturalTransformation
  (\a => component natTrans (mapObj fun1 a))
  (\a, b, f => commutativity natTrans _ _ (mapMor fun1 a b f))
