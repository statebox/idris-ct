\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module Basic.Adjunction
>
> import Basic.Category as Cat
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Dual.DualCategory
> import Dual.DualFunctor
> import Idris.TypesAsCategoryExtensional as Idris
> import Product.ProductCategory
> import Product.ProductFunctor
> import Profunctors.HomFunctor
> import Utils
>
> %access public export
> %default total
>
> Adjunction : (cat1, cat2 : Category) -> CFunctor cat2 cat1 -> CFunctor cat1 cat2 -> Type
> Adjunction cat1 cat2 funL funR = NaturalIsomorphism
>   (productCategory (dualCategory cat2) cat1)
>   Idris.typesAsCategoryExtensional
>   (costar funL)
>   (star funR)

phi id_funLa; funR (funL f) = f; phi id_funLb
-- comm f g h := f; (phi h; funR g) = phi (funL f; (h; g))
-- comm f g h := phi (a,b); Hom(f, funR g) = Hom(funL f, g); phi (a', b')
id_a; (phi id_funLa; funR (funL f)) = phi (funL id_a; (id_funLa; funL f))
f; (phi id_funLb; funR id_funLb) = phi (funL f; (id_funLb; id_funLb))

> {-
> unit : {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> Adjunction cat1 cat2 funL funR
>     -> NaturalTransformation cat2 cat2 (idFunctor cat2) (functorComposition cat2 cat1 cat2 funL funR)
> unit {cat1} {cat2} {funL} {funR} adj = MkNaturalTransformation
>   (\a => func (component (morphism adj) (a, mapObj funL a)) (identity cat1 (mapObj funL a)))
>   (\a, b, f =>
>     trans (sym (leftIdentity cat2 a _ _))
>     (trans (comm (identity cat2 a) (mapMor funL a b f) (identity cat1 (mapObj funL a)))
>     (trans (cong
>       (trans (cong2 (preserveId funL a) (Refl { x = compose cat1 _ _ _ _ (mapMor funL a b f) }))
>       (trans (leftIdentity cat1 (mapObj funL a) _ _)
>       (trans (leftIdentity cat1 (mapObj funL a) _ _)
>       (trans (sym (rightIdentity cat1 _ _ _))
>       (cong (sym (rightIdentity cat1 (mapObj funL b) _ _))))))))
>     (trans (sym (comm f (identity cat1 (mapObj funL b)) (identity cat1 (mapObj funL b))))
>     (cong (trans (cong (preserveId funR _)) (rightIdentity cat2 _ _ _)))))))
> -}

Inv id_funRa . f = funL (funR f) . Inv id_funRb
-- invComm f g h := funL f . (Inv h . g) = Inv (f . (h . funR g))
funL id_funRa . (Inv id_funRa . f) = Inv (id_funRa . (id_funRa . funR f))
funL (funR f) . (Inv id_funRb . id_b) = Inv (funR f . (id_funRb . funR id_b))

> {-
> counit : {cat1, cat2 : Category}
>       -> {funL : CFunctor cat2 cat1}
>       -> {funR : CFunctor cat1 cat2}
>       -> Adjunction cat1 cat2 funL funR
>       -> NaturalTransformation cat1 cat1 (functorComposition cat1 cat2 cat1 funR funL) (idFunctor cat1)
> counit {cat1} {cat2} {funL} {funR} adj = MkNaturalTransformation
>   (\b => func (Inverse (homIsomorphism adj (mapObj funR b) b)) (identity cat2 (mapObj funR b)))
>   (\a, b, f =>
>     trans (sym (leftIdentity cat1 _ _ _))
>     (trans (cong2 (sym (preserveId funL _)) (Refl {x=compose cat1 _ _ _ _ f}))
>     (trans (adjunctionInverseCommutativity adj (identity cat2 (mapObj funR a)) f (identity cat2 (mapObj funR a)))
>     (trans (cong
>       (trans (leftIdentity cat2 (mapObj funR a) _ _)
>       (trans (leftIdentity cat2 (mapObj funR a) _ _)
>       (trans (sym (rightIdentity cat2 _ _ _))
>       (cong (trans (sym (rightIdentity cat2 _ _ _)) (cong (sym (preserveId funR b)))))))))
>     (trans (sym (adjunctionInverseCommutativity adj
>                   (mapMor funR a b f) (identity cat1 b) (identity cat2 (mapObj funR b))))
>     (cong (rightIdentity cat1 _ _ _)))))))
> -}
