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

> module Hom.HomFunctor
>
> import Basic.Category
> import Basic.Functor
> import Dual.DualCategory
> import Dual.DualFunctor
> import Idris.TypesAsCategoryExtensional as Idris
> import Product.ProductCategory
> import Product.ProductFunctor
> import Profunctors.Profunctor
>
> %access public export
> %default total
>
> homFunctor : (cat : Category) -> Profunctor cat cat
> homFunctor cat = MkCFunctor
>   (\a => mor cat (fst a) (snd a))
>   (\a, b, f => MkExtensionalTypeMorphism (\h => compose cat (fst b) (fst a) (snd b)
>                                                             (pi1 f)
>                                                             (compose cat (fst a) (snd a) (snd b) h (pi2 f))))
>   (\a => funExt (\x => trans (leftIdentity cat (fst a) (snd a) _) (rightIdentity cat (fst a) (snd a) x)))
>   (\a, b, c, f, g => funExt (\x =>
>     trans (sym (associativity cat _ _ _ _ (pi1 g) (pi1 f) _))
>           (cong (trans (cong (associativity cat _ _ _ _ x (pi2 f) (pi2 g)))
>                        (associativity cat _ _ _ _ (pi1 f) _ (pi2 g))))))

postCompose cat a is Hom(a,–), it takes a morphism g to \f => (f; g)

> postCompose : (cat : Category) -> (a : obj cat) -> CFunctor cat Idris.typesAsCategoryExtensional
> postCompose cat a = MkCFunctor
>   (\b => mor cat a b)
>   (\b, c, g => MkExtensionalTypeMorphism (\f => compose cat a b c f g))
>   (\b => funExt (\f => rightIdentity cat a b f))
>   (\b, c, d, g, h => funExt (\f => associativity cat a b c d f g h))

preCompose cat a is Hom(–,a), it takes a morphism g to \f => (g; f)

> preCompose : (cat : Category) -> (a : obj cat) -> CFunctor (dualCategory cat) Idris.typesAsCategoryExtensional
> preCompose cat a = MkCFunctor
>   (\b => mor cat b a)
>   (\b, c, g => MkExtensionalTypeMorphism (\f => compose cat c b a g f))
>   (\b => funExt (\f => leftIdentity cat b a f))
>   (\b, c, d, g, h => funExt (\f => sym (associativity cat d c b a h g f)))

costar f takes f : C -> D to D(f, 1)

> costar : {cat1, cat2 : Category}
>       -> CFunctor cat1 cat2
>       -> Profunctor cat2 cat1
> costar {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor f) (idFunctor cat2)) (homFunctor cat2)

star f takes f : C -> D to D(1, f)

> star : {cat1, cat2 : Category}
>     -> CFunctor cat1 cat2
>     -> Profunctor cat1 cat2
> star {cat2} f = functorComposition _ _ _ (productFunctor (dualFunctor (idFunctor cat2)) f) (homFunctor cat2)
