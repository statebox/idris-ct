> module Booleans.Booleans
>
> import Basic.Category
>
> %access public export
> %default total
>
> data BoolArr : Bool -> Bool -> Type where
>   FId : BoolArr False False
>   F2T : BoolArr False True
>   TId : BoolArr True  True
>
> uniqueBoolArr : (a, b : Bool) -> (f, g : BoolArr a b) -> f = g
> uniqueBoolArr False False FId FId = Refl
> uniqueBoolArr False True  F2T F2T = Refl
> uniqueBoolArr True  True  TId TId = Refl
>
> boolId : (b : Bool) -> BoolArr b b
> boolId False = FId
> boolId True = TId
>
> boolCompose : BoolArr a b -> BoolArr b c -> BoolArr a c
> boolCompose FId f = f
> boolCompose f TId = f
>
> boolLeftIdentity : (a : Bool) -> (b : Bool) -> (f : BoolArr a b) -> boolCompose (boolId a) f = f
> boolLeftIdentity False b f = Refl
> boolLeftIdentity True True TId = Refl
>
> boolRightIdentity : (a : Bool) -> (b : Bool) -> (f : BoolArr a b) -> boolCompose f (boolId b) = f
> boolRightIdentity a True f = Refl
> boolRightIdentity False False FId = Refl
>
> boolAssociativity : (a : Bool) -> (b : Bool) -> (c : Bool) -> (d : Bool)
>                  -> (f : BoolArr a b) -> (g : BoolArr b c) -> (h : BoolArr c d)
>                  -> boolCompose f (boolCompose g h) = boolCompose (boolCompose f g) h
> boolAssociativity _ _ _ _ FId _ _ = Refl
> boolAssociativity _ _ _ _ _ _ TId = Refl

The (pre)order of booleans, often referred to as just "2".

> Booleans : Category
> Booleans = MkCategory Bool BoolArr boolId (\_, _, _ => boolCompose) boolLeftIdentity boolRightIdentity boolAssociativity
