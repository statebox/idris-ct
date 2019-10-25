module Higher.Bicategory

import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import Product.ProductCategory
import Product.ProductFunctor

public export
horizontalIdPostcomposition : {cat1, cat2, cat3 : Category}
                           -> (obj cat2)
                           -> (hc : CFunctor (productCategory cat1 cat2) cat3)
                           -> CFunctor cat1 cat3
horizontalIdPostcomposition {cat1} {cat2} identityMorphism hc = MkCFunctor
  (\a => mapObj hc (a, identityMorphism))
  (\a, b, f => mapMor hc
                      (a, identityMorphism)
                      (b, identityMorphism)
                      (MkProductMorphism f (identity cat2 identityMorphism)))
  (\a => preserveId hc (a, identityMorphism))
  (\a, b, c, f, g => let pc = preserveCompose hc
                                              (a, identityMorphism)
                                              (b, identityMorphism)
                                              (c, identityMorphism)
                                              (MkProductMorphism f (identity cat2 identityMorphism))
                                              (MkProductMorphism g (identity cat2 identityMorphism))
                     in trans (cong (\x => mapMor hc
                                                  (a, identityMorphism)
                                                  (c, identityMorphism)
                                                  (MkProductMorphism (compose cat1 a b c f g) x))
                                    (sym $ leftIdentity cat2
                                                        identityMorphism
                                                        identityMorphism
                                                        (identity cat2 identityMorphism)))
                              pc)

horizontalIdPrecomposition : {cat1, cat2, cat3 : Category}
                          -> (obj cat1)
                          -> (hc : CFunctor (productCategory cat1 cat2) cat3)
                          -> CFunctor cat2 cat3
horizontalIdPrecomposition {cat1} {cat2} {cat3} identityMorphism hc = horizontalIdPostcomposition
  identityMorphism
  (functorComposition (productCategory cat2 cat1)
                      (productCategory cat1 cat2)
                      cat3
                      flipFunctor
                      hc)

leftAssociator : {cat1, cat2, cat3, cat4, cat5 : Category}
              -> CFunctor (productCategory cat2 cat3) cat5
              -> CFunctor (productCategory cat1 cat5) cat4
              -> CFunctor (productCategory cat1 (productCategory cat2 cat3)) cat4
leftAssociator {cat1} {cat2} {cat3} {cat4} {cat5} f g = functorComposition
  (productCategory cat1 (productCategory cat2 cat3))
  (productCategory cat1 cat5)
  cat4
  (productFunctor (idFunctor cat1) f)
  g

rightAssociator : {cat1, cat2, cat3, cat4, cat5 : Category}
               -> CFunctor (productCategory cat1 cat2) cat5
               -> CFunctor (productCategory cat5 cat3) cat4
               -> CFunctor (productCategory cat1 (productCategory cat2 cat3)) cat4
rightAssociator {cat1} {cat2} {cat3} {cat4} {cat5} f g = functorComposition
  (productCategory cat1 (productCategory cat2 cat3))
  (productCategory (productCategory cat1 cat2) cat3)
  cat4
  (productAssociator cat1 cat2 cat3)
  (functorComposition (productCategory (productCategory cat1 cat2) cat3)
                      (productCategory cat5 cat3)
                      cat4
                      (productFunctor f (idFunctor cat3))
                      g)

record Bicategory where
  constructor MkBicategory
  cell0                 : Type
  cell1                 : cell0 -> cell0 -> Category
  identity1cell         : (x : cell0) -> obj (cell1 x x)
  horizontalComposition : {x, y, z : cell0}
                       -> CFunctor (productCategory (cell1 x y) (cell1 y z)) (cell1 x z)
  leftUnitor            : {x, y : cell0}
                       -> NaturalIsomorphism (cell1 x y)
                                             (cell1 x y)
                                             (horizontalIdPrecomposition (identity1cell x) horizontalComposition)
                                             (idFunctor (cell1 x y))
  rightUnitor           : {x, y : cell0}
                       -> NaturalIsomorphism (cell1 x y)
                                             (cell1 x y)
                                             (horizontalIdPostcomposition (identity1cell y) horizontalComposition)
                                             (idFunctor (cell1 x y))
  associator            : {w, x, y, z : cell0}
                       -> NaturalIsomorphism (productCategory (cell1 w x)
                                                              (productCategory (cell1 x y) (cell1 y z)))
                                             (cell1 w z)
                                             (leftAssociator horizontalComposition horizontalComposition {cat1 = cell1 w x} {cat2 = cell1 x y} {cat3 = cell1 y z} {cat4 = cell1 w z})
                                             (rightAssociator horizontalComposition horizontalComposition {cat1 = cell1 w x} {cat2 = cell1 x y} {cat3 = cell1 y z} {cat4 = cell1 w z})
