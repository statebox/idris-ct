module CoLimits.Pushout

import Basic.Category
import CoLimits.CoLimit
import CommutativeDiagram.Diagram
import Span.Span

public export
Pushout : {cat : Category}
       -> {x, y, z : obj cat}
       -> (f : mor cat z x)
       -> (g : mor cat z y)
       -> Type
Pushout {cat} {x} {y} {z} f g = CoLimit SpanIndexCategory cat (fst $ span x y z f g)

public export
HasPushouts : (cat : Category) -> Type
HasPushouts cat = {x, y, z : obj cat}
               -> (f : mor cat z x)
               -> (g : mor cat z y)
               -> Pushout {cat} {x} {y} {z} f g
