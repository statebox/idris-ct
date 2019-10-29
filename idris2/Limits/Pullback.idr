module Limits.Pullback

import Basic.Category
import CoLimits.Pushout
import Dual.DualCategory

public export
Pullback : {cat : Category}
        -> {x, y, z : obj cat}
        -> (f : mor cat x z)
        -> (g : mor cat y z)
        -> Type
Pullback {cat} {x} {y} {z} f g = Pushout {cat = dualCategory cat} {x} {y} {z} f g

public export
HasPullbacks : (cat : Category) -> Type
HasPullbacks cat = (x, y, z : obj cat)
                -> (f : mor cat x z)
                -> (g : mor cat y z)
                -> Pullback {cat} {x} {y} {z} f g
