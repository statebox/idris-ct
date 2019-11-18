module MonoidalCategory.SymmetricMonoidalCategoryHelpers

import Utils
import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import Basic.NaturalTransformation
import MonoidalCategory.MonoidalCategoryHelpers
import Product.ProductCategory

public export
swapMorphisms :
     (a, b : (obj cat1, obj cat2))
  -> mor (productCategory cat1 cat2) a b
  -> mor (productCategory cat2 cat1) (swap a) (swap b)
swapMorphisms (a1, a2) (b1, b2) (MkProductMorphism pi1 pi2) = MkProductMorphism pi2 pi1

public export
swapFunctor : (cat1, cat2 : Category) -> CFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor cat1 cat2 = MkCFunctor
  swap
  swapMorphisms
  (\a12 => case a12 of
             (a1,a2) => Refl)
  swapCompose
  where
  swapCompose : (a, b, c : (obj cat1, obj cat2)) -> (f : ProductMorphism cat1 cat2 a b) -> (g : ProductMorphism cat1 cat2 b c) ->
                swapMorphisms a c (MkProductMorphism (compose cat1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
                                                     (compose cat2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g))) =
                  MkProductMorphism (compose cat2 (fst (swap a)) (fst (swap b)) (fst (swap c)) (pi1 (swapMorphisms a b f)) (pi1 (swapMorphisms b c g)))
                                    (compose cat1 (snd (swap a)) (snd (swap b)) (snd (swap c)) (pi2 (swapMorphisms a b f)) (pi2 (swapMorphisms b c g)))
  swapCompose (a1, a2) (b1, b2) (c1, c2) (MkProductMorphism f1 f2) (MkProductMorphism g1 g2) = Refl

public export
UnitCoherence :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (unit : obj cat)
  -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat))
  -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat))
  -> (symmetry : NaturalIsomorphism (productCategory cat cat)
                                    cat
                                    tensor
                                    (functorComposition (productCategory cat cat)
                                                        (productCategory cat cat)
                                                        cat
                                                        (swapFunctor cat cat)
                                                        tensor))
  -> (a : obj cat)
  -> Type
UnitCoherence cat tensor unit leftUnitor rightUnitor symmetry a =
  (component (natTrans rightUnitor) a) =
  (compose cat
           (mapObj tensor (a, unit))
           (mapObj tensor (unit, a))
           a
           (component (natTrans symmetry) (a, unit))
           (component (natTrans leftUnitor) a))

public export
associativityLeft :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (associator : Associator cat tensor)
  -> (symmetry : NaturalIsomorphism (productCategory cat cat)
                                    cat
                                    tensor
                                    (functorComposition (productCategory cat cat)
                                                        (productCategory cat cat)
                                                        cat
                                                        (swapFunctor cat cat)
                                                        tensor))
  -> (a, b, c : obj cat)
  -> mor cat (mapObj tensor (mapObj tensor (a, b), c)) (mapObj tensor (b, mapObj tensor (c, a)))
associativityLeft cat tensor associator symmetry a b c =
  compose cat
          (mapObj tensor (mapObj tensor (a, b), c))
          (mapObj tensor (a, mapObj tensor (b, c)))
          (mapObj tensor (b, mapObj tensor (c, a)))
          (component (natTrans associator) (a, b, c))
          (compose cat
                   (mapObj tensor (a, mapObj tensor (b, c)))
                   (mapObj tensor (mapObj tensor (b, c), a))
                   (mapObj tensor (b, mapObj tensor (c, a)))
                   (component (natTrans symmetry) (a, mapObj tensor (b, c)))
                   (component (natTrans associator) (b, c, a)))

public export
associativityRight :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (associator : Associator cat tensor)
  -> (symmetry : NaturalIsomorphism (productCategory cat cat)
                                    cat
                                    tensor
                                    (functorComposition (productCategory cat cat)
                                                        (productCategory cat cat)
                                                        cat
                                                        (swapFunctor cat cat)
                                                        tensor))
  -> (a, b, c : obj cat)
  -> mor cat (mapObj tensor (mapObj tensor (a, b), c)) (mapObj tensor (b, mapObj tensor (c, a)))
associativityRight cat tensor associator symmetry a b c =
  compose cat
          (mapObj tensor (mapObj tensor (a, b), c))
          (mapObj tensor (mapObj tensor (b, a), c))
          (mapObj tensor (b, mapObj tensor (c, a)))
          (mapMor tensor
                  (mapObj tensor (a, b), c)
                  (mapObj tensor (b, a), c)
                  (MkProductMorphism (component (natTrans symmetry) (a, b)) (identity cat c)))
          (compose cat
                   (mapObj tensor (mapObj tensor (b, a), c))
                   (mapObj tensor (b, mapObj tensor (a, c)))
                   (mapObj tensor (b, mapObj tensor (c, a)))
                   (component (natTrans associator) (b, a, c))
                   (mapMor tensor
                           (b, mapObj tensor (a, c))
                           (b, mapObj tensor (c, a))
                           (MkProductMorphism (identity cat b) (component (natTrans symmetry) (a, c)))))

public export
AssociativityCoherence :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (associator : Associator cat tensor)
  -> (symmetry : NaturalIsomorphism (productCategory cat cat)
                                    cat
                                    tensor
                                    (functorComposition (productCategory cat cat)
                                                        (productCategory cat cat)
                                                        cat
                                                        (swapFunctor cat cat)
                                                        tensor))
  -> (a, b, c : obj cat)
  -> Type
AssociativityCoherence cat tensor associator symmetry a b c =
  associativityLeft  cat tensor associator symmetry a b c =
  associativityRight cat tensor associator symmetry a b c

public export
InverseLaw :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (symmetry : NaturalIsomorphism (productCategory cat cat)
                                    cat
                                    tensor
                                    (functorComposition (productCategory cat cat)
                                                        (productCategory cat cat)
                                                        cat
                                                        (swapFunctor cat cat)
                                                        tensor))
  -> (a, b : obj cat)
  -> Type
InverseLaw cat tensor symmetry a b =
  (compose cat
           (mapObj tensor (a, b))
           (mapObj tensor (b, a))
           (mapObj tensor (a, b))
           (component (natTrans symmetry) (a, b))
           (component (natTrans symmetry) (b, a))) =
  (identity cat (mapObj tensor (a, b)))
