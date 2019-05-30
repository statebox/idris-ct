> module Basic.Limits
>
> import Basic.Category
>
> %access public export
> %default total
>
> record TerminalObject (cat : Category) where
>   constructor MkTerminalObject
>   Carrier : obj cat
>   exists : (x : obj cat) -> mor cat x Carrier
>   unique : (x : obj cat) -> (f : mor cat x Carrier) -> f = exists x
>
> record CommutativeMorphism (cat : Category) 
>                            (x : obj cat) (a : obj cat) (b : obj cat) (Carrier : obj cat) 
>                            (pi1 : mor cat Carrier a) (pi2 : mor cat Carrier b) 
>                            (f : mor cat x a) (g : mor cat x b) where
>   constructor MkCommutativeMorphism
>   Challenger : mor cat x Carrier
>   commutativityL: compose cat x Carrier a Challenger pi1 = f
>   commutativityR: compose cat x Carrier b Challenger pi2 = g
>
> record Product (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkProduct
>   Carrier : obj cat
>   pi1 : mor cat Carrier a
>   pi2 : mor cat Carrier b
>   exists : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b) -> CommutativeMorphism cat x a b Carrier pi1 pi2 f g
>   unique : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b) 
>         -> (h : CommutativeMorphism cat x a b Carrier pi1 pi2 f g) -> h = exists x f g
>

exists 
         h
         |
a <-f- Carrier -g-> b

commutativity (?y) <=> h(a) = (f(a), g(a)) = exists(a)

h arbitrary => h(a) = (h1(a), h2(a))