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

> module Discrete.FunctionAsFunctor
>
> import Basic.Category
> import Basic.Functor
> import Discrete.DiscreteCategory
>
> %access public export
> %default total
>
> functionMapMor : (f : a -> b) -> (x, y : a) -> DiscreteMorphism x y -> DiscreteMorphism (f x) (f y)
> functionMapMor f x x Refl = Refl
>
> functionPreserveCompose :
>      (f : a -> b)
>   -> (x, y, z : a)
>   -> (g : DiscreteMorphism x y)
>   -> (h : DiscreteMorphism y z)
>   -> functionMapMor f x z (discreteCompose x y z g h)
>    = discreteCompose (f x) (f y) (f z) (functionMapMor f x y g) (functionMapMor f y z h)
> functionPreserveCompose f x x x Refl Refl = Refl
>
> functionAsFunctor :
>      (f : a -> b)
>   -> CFunctor (discreteCategory a) (discreteCategory b)
> functionAsFunctor f = MkCFunctor
>   f
>   (functionMapMor f)
>   (\_ => Refl)
>   (functionPreserveCompose f)
