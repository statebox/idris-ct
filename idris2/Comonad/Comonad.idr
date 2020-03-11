module Comonad.Comonad

import Basic.Category
import Dual.DualCategory
import Monad.Monad

public export
Comonad : (cat : Category) -> Type
Comonad cat = Monad (dualCategory cat)
