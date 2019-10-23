module MonoidalCategory.MonoidalCategoryHelpers

import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import Basic.NaturalTransformation
import Product.ProductCategory
import Product.ProductFunctor
import Utils

public export
leftTensor3 :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> CFunctor (productCategory cat (productCategory cat cat)) cat
leftTensor3 cat tensor = functorComposition (productCategory cat (productCategory cat cat))
                                            (productCategory (productCategory cat cat) cat)
                                            cat
                                            (productAssociator cat cat cat)
                                            (functorComposition (productCategory (productCategory cat cat) cat)
                                                                (productCategory cat cat)
                                                                cat
                                                                (productFunctor tensor (idFunctor cat))
                                                                tensor)

public export
rightTensor3 :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> CFunctor (productCategory cat (productCategory cat cat)) cat
rightTensor3 cat tensor = functorComposition (productCategory cat (productCategory cat cat))
                                             (productCategory cat cat)
                                             cat
                                             (productFunctor (idFunctor cat) tensor)
                                             tensor

public export
Associator :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> Type
Associator cat tensor = NaturalIsomorphism (productCategory cat (productCategory cat cat))
                                           cat
                                           (leftTensor3  cat tensor)
                                           (rightTensor3 cat tensor)

public export
leftIdTensor :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (unit : obj cat)
  -> CFunctor cat cat
leftIdTensor cat tensor unit = MkCFunctor
  (\a => mapObj tensor (unit, a))
  (\a, b, f => mapMor tensor (unit, a) (unit, b) (MkProductMorphism (identity cat unit) f))
  (\a => preserveId tensor (unit, a))
  (\a, b, c, f, g => trans (cong (mapMor tensor (unit, a) (unit, c))
                                 (cong2 MkProductMorphism
                                        (sym (leftIdentity cat unit unit (identity cat unit)))
                                        Refl))
                           (preserveCompose tensor
                                            (unit, a)
                                            (unit, b)
                                            (unit, c)
                                            (MkProductMorphism (identity cat unit) f)
                                            (MkProductMorphism (identity cat unit) g)))

public export
rightIdTensor :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (unit : obj cat)
  -> CFunctor cat cat
rightIdTensor cat tensor unit = MkCFunctor
  (\a => mapObj tensor (a, unit))
  (\a, b, f => mapMor tensor (a, unit) (b, unit) (MkProductMorphism f (identity cat unit)))
  (\a => preserveId tensor (a, unit))
  (\a, b, c, f, g => trans (cong (mapMor tensor (a, unit) (c, unit))
                                 (cong2 MkProductMorphism
                                        Refl
                                        (sym (leftIdentity cat unit unit (identity cat unit)))))
                           (preserveCompose tensor
                                            (a, unit)
                                            (b, unit)
                                            (c, unit)
                                            (MkProductMorphism f (identity cat unit))
                                            (MkProductMorphism g (identity cat unit))))

public export
MonoidalPentagon :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (associator : Associator cat tensor)
  -> (a, b, c, d : obj cat)
  -> Type
MonoidalPentagon cat tensor associator a b c d =
  (compose cat
           (mapObj tensor (mapObj tensor (mapObj tensor (a, b), c), d))
           (mapObj tensor (mapObj tensor (a, b), mapObj tensor (c, d)))
           (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d)))))
           (component (natTrans associator) (mapObj tensor (a, b), c, d))
           (component (natTrans associator) (a, b, mapObj tensor (c, d))))
           =
  (compose cat
           (mapObj tensor (mapObj tensor (mapObj tensor (a, b), c), d))
           (mapObj tensor (mapObj tensor (a, mapObj tensor (b, c)), d))
           (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d)))))
           (mapMor tensor
                   (mapObj tensor (mapObj tensor (a, b), c), d)
                   (mapObj tensor (a, mapObj tensor (b, c)), d)
                   (MkProductMorphism (component (natTrans associator) (a, b, c)) (identity cat d)))
           (compose cat
                    (mapObj tensor (mapObj tensor (a, mapObj tensor (b, c)),d))
                    (mapObj tensor (a, mapObj tensor (mapObj tensor (b, c), d)))
                    (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d)))))
                    (component (natTrans associator) (a, mapObj tensor (b, c), d))
                    (mapMor tensor
                            (a, mapObj tensor (mapObj tensor (b, c), d))
                            (a, (mapObj tensor (b, mapObj tensor (c, d))))
                            (MkProductMorphism (identity cat a) (component (natTrans associator) (b, c, d))))))

public export
MonoidalTriangle :
     (cat : Category)
  -> (tensor : CFunctor (productCategory cat cat) cat)
  -> (unit : obj cat)
  -> (associator : Associator cat tensor)
  -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat))
  -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat))
  -> (a, b : obj cat)
  -> Type
MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b =
  (mapMor tensor
          (mapObj tensor (a, unit), b)
          (a, b)
          (MkProductMorphism (component (natTrans rightUnitor) a) (identity cat b)))
          =
  (compose cat
           (mapObj tensor (mapObj tensor (a, unit), b))
           (mapObj tensor (a, mapObj tensor (unit, b)))
           (mapObj tensor (a, b))
           (component (natTrans associator) (a, unit, b))
           (mapMor tensor
                   (a, mapObj tensor (unit, b))
                   (a, b)
                   (MkProductMorphism (identity cat a) (component (natTrans leftUnitor) b))))