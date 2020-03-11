module Profunctors.Profunctor

import Basic.Category
import Basic.Functor
import Dual.DualCategory
import Idris.TypesAsCategoryExtensional
import Product.ProductCategory

public export
Profunctor : Category -> Category -> Type
Profunctor c d = CFunctor (productCategory (dualCategory d) c) typesAsCategoryExtensional
