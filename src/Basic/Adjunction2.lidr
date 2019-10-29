> module Basic.Adjunction2
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Basic.Adjunction
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Idris.TypesAsCategory as Idris
> import Utils
>
> homIsomorphism :
>      (cat1, cat2 : Category)
>   -> (funL : CFunctor cat2 cat1)
>   -> (funR : CFunctor cat1 cat2)
>   -> Adjunction cat1 cat2 funL funR
>   -> (a : obj cat2)
>   -> (b : obj cat1)
>   -> Isomorphism Idris.typesAsCategory (mor cat1 (mapObj funL a) b) (mor cat2 a (mapObj funR b))
> homIsomorphism cat1 cat2 funL funR adj a b = MkIsomorphism
>   (\la2b => compose cat2 _ _ _ (component (unit adj) a) (mapMor funR _ _ la2b))
>   (\a2rb => compose cat1 _ _ _ (mapMor funL _ _ a2rb) (component (counit adj) b))
>   ?ll
>   ?r
>
> naturalTransformationExtInv :
>      {cat1, cat2 : Category}
>   -> {fun1, fun2 : CFunctor cat1 cat2}
>   -> {trans1, trans2 : NaturalTransformation cat1 cat2 fun1 fun2}
>   -> trans1 = trans2
>   -> (a : obj cat1)
>   -> component trans1 a = component trans2 a
> naturalTransformationExtInv eq a = cong {f=\x => component x a} eq
>
> l : (cat1, cat2 : Category)
>   -> (funL : CFunctor cat2 cat1)
>   -> (funR : CFunctor cat1 cat2)
>   -> Adjunction cat1 cat2 funL funR
>   -> (a : obj cat2)
>   -> (b : obj cat1)
>   -> (la2b : mor cat1 (mapObj funL a) b)
>   -> compose cat1 _ _ _ (compose cat1 _ _ _ (mapMor funL _ _ (component (unit adj) a)) (component (counit adj) (mapObj funL a))) la2b = la2b
> l cat1 cat2 funL funR adj a b la2b =
>       --((((cong2 (preserveCompose funL _ _ _ (component (unit adj) a) (mapMor funR _ _ la2b)) Refl `trans`
>       --associativity cat2 _ _ _ _ (mapMor funL _ _ (component (unit adj) a)) (mapMor funL _ _ (mapMor funR _ _ la2b)) (component (counit adj) b)) `trans`
>       --cong (sym (commutativity (counit adj) _ _ la2b))) `trans`
>       --associativity cat2 _ _ _ _ (mapMor funL _ _ (component (unit adj) a)) (component (counit adj) (mapObj funL a)) la2b) `trans`
>       cong2 (sym (naturalTransformationExtInv (leftCounitUnitEq adj) a)) (Refl { x = la2b }) `trans`
>       leftIdentity cat1 _ _ la2b



l : (la2b => funL (unit a . funR la2b) . counit b) = id
(funL (unit a) . funL (funR la2b)) . counit b
funL (unit a) . (funL (funR la2b) . counit b)
funL (unit a) . (counit (funL a) . la2b)
(funL (unit a) . counit (funL a)) . la2b
id_funLa . la2b
