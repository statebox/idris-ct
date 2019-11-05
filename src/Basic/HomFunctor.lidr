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

> module Basic.HomFunctor
>
> import Basic.Category as Cat
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Dual.DualCategory as D
> import Idris.TypesAsCategoryExtensional as Idris
> import Product.ProductCategory as P
>
> HomFunctor : (cat : Category) -> CFunctor (P.productCategory (D.dualCategory cat) cat) Idris.typesAsCategoryExtensional
> HomFunctor cat = MkCFunctor
>   (\a => mor cat (fst a) (snd a))
>   (\a, b, f => MkExtensionalTypeMorphism (\h => compose cat (fst b) (fst a) (snd b) (pi1 f) (compose cat (fst a) (snd a) (snd b) h (pi2 f))))
>   (\a => funExt (\x => trans (leftIdentity cat (fst a) _ _) (rightIdentity cat (fst a) (snd a) x)))
>   (\a, b, c, f, g => funExt (\x =>
>     trans (sym (associativity cat _ _ _ _ (pi1 g) (pi1 f) _))
>     (cong (
>       trans (cong (associativity cat _ _ _ _ x (pi2 f) (pi2 g)))
>       (associativity cat _ _ _ _ (pi1 f) _ (pi2 g))))))
