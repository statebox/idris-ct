module MonoidalCategory.MonoidalCategory

import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import MonoidalCategory.MonoidalCategoryHelpers
import Product.ProductCategory

public export
record MonoidalCategory where
  constructor MkMonoidalCategory
  cat : Category
  tensor : CFunctor (productCategory cat cat) cat
  unit : obj cat
  associator : Associator cat tensor
  leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat)
  rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat)
  pentagonEq : (a, b, c, d : obj cat) -> MonoidalPentagon cat tensor associator a b c d
  triangleEq : (a, b : obj cat) -> MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b
