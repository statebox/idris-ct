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

> module Discrete.DiscreteFunctor
>
> import Basic.Category
> import Basic.Functor
> import Discrete.DiscreteCategory
>
> %access public export
> %default total
>
> discreteMapMor :
>      (f : a -> obj cat)
>   -> (x, y : a)
>   -> DiscreteMorphism x y
>   -> mor cat (f x) (f y)
> discreteMapMor {cat} f x x Refl = identity cat (f x)
>
> discretePreserveCompose :
>      (f : a -> obj cat)
>   -> (x, y, z : a)
>   -> (g : x = y)
>   -> (h : y = z)
>   -> discreteMapMor f x z (discreteCompose x y z g h)
>    = compose cat (f x) (f y) (f z) (discreteMapMor f x y g) (discreteMapMor f y z h)
> discretePreserveCompose {cat} f x x x Refl Refl = (sym (leftIdentity cat _ _ _))
>
> discreteFunctor : (f : a -> obj cat) -> CFunctor (discreteCategory a) cat
> discreteFunctor {a} {cat} f = MkCFunctor
>   f
>   (discreteMapMor {a} {cat} f)
>   (\_ => Refl)
>   (discretePreserveCompose {a} {cat} f)
