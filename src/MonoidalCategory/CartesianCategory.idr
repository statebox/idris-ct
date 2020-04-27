import Basic.Category
import Basic.Functor
import Basic.NaturalIsomorphism
import Limits.FiniteProduct
import Limits.Product
import Limits.TerminalObject
import MonoidalCategory.MonoidalCategory
import MonoidalCategory.MonoidalCategoryHelpers
import Product.ProductCategory

%access public export
%default total

cartesianCategory : FiniteProduct cat -> MonoidalCategory
cartesianCategory {cat} (MkFiniteCoProduct binaryProduct terminalObject) =
  MkMonoidalCategory
    cat
    tensor
    unit
    associator
    leftUnitor
    rightUnitor
    (\a, b, c, d => monoidalPentagon {a} {b} {c} {d})
    monoidalTriangle
where
  tensor : CFunctor (productCategory cat cat) cat
  tensor = binaryProductToFunctor binaryProduct

  unit : obj cat
  unit = carrier terminalObject

  associator : Associator cat tensor
  associator = ?associator_rhs

  leftUnitor : NaturalIsomorphism cat cat (leftIdTensor cat tensor unit) (idFunctor cat)
  leftUnitor = ?leftUnitor_rhs

  rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat)
  rightUnitor = ?rightUnitor_rhs

  monoidalPentagon : MonoidalPentagon cat tensor associator a b c d
  monoidalPentagon = ?monoidalPentagon_rhs

  monoidalTriangle : MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b
  monoidalTriangle = ?monoidalTriangle_rhs
