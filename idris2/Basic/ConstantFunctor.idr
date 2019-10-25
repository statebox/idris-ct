module Basic.ConstantFunctor

import Basic.Category
import Basic.Functor

public export
Delta : (cat1, cat2 : Category) -> (n : obj cat2) -> CFunctor cat1 cat2
Delta cat1 cat2 n = MkCFunctor
  (\a => n)
  (\a, b, f => identity cat2 n)
  (\a => Refl)
  (\a, b, c, f, g => sym (leftIdentity cat2 n n (identity cat2 n)))