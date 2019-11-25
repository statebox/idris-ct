> module Booleans.BooleanCoLimits
>
> import Basic.Category
> import CoLimits.InitialObject
> import CoLimits.CoProduct
> import Booleans.Booleans
>
> %access public export
> %default total
>
> boolInitializer : (b : Bool) -> BoolArr False b
> boolInitializer False = FId
> boolInitializer True  = F2T
>
> falseIsInitial : InitialObject Booleans
> falseIsInitial = MkInitialObject False boolInitializer (uniqueBoolArr False)
>
> boolInl : (a : Bool) -> (b : Bool) -> BoolArr a (a || b)
> boolInl False False = FId
> boolInl False True  = F2T
> boolInl True  _     = TId
>
> boolInr : (a : Bool) -> (b : Bool) -> BoolArr b (a || b)
> boolInr False False = FId
> boolInr True  False = F2T
> boolInr False True  = TId
> boolInr True  True  = TId
>
> boolCoProductExists : (a : Bool) -> (b : Bool) -> (c : Bool)
>                    -> (f : BoolArr a c) -> (g : BoolArr b c)
>                    -> CommutingMorphism Booleans a b (a || b) c (boolInl a b) (boolInr a b) f g
> boolCoProductExists False False c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolCoProductExists False True  c f g = MkCommutingMorphism g (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
> boolCoProductExists True  b     c f g = MkCommutingMorphism f (uniqueBoolArr _ _ _ _) (uniqueBoolArr _ _ _ _)
>
> orIsCoproduct : (a : Bool) -> (b : Bool) -> CoProduct Booleans a b
> orIsCoproduct a b = MkCoProduct (a || b) (boolInl a b) (boolInr a b) (boolCoProductExists a b)
>   (\_, _, _, _ => uniqueBoolArr _ _ _ _)
