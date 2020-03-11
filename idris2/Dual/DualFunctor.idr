module Dual.DualFunctor

import Basic.Category
import Basic.Functor
import Dual.DualCategory

public export
dualFunctor :
     CFunctor cat1 cat2
  -> CFunctor (dualCategory cat1) (dualCategory cat2)
dualFunctor func = MkCFunctor
  (\a => (mapObj func a))
  (\a, b, f => (mapMor func b a f))
  (\a => preserveId func a)
  (\a, b, c, f, g => (preserveCompose func c b a g f))
