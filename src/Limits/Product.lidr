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

> module Limits.Product
>
> import Basic.Category
>
> %access public export
> %default total
> %auto_implicits off
>
> record CommutingMorphism (cat : Category)
>                          (x : obj cat) (a : obj cat) (b : obj cat) (carrier : obj cat)
>                          (pi1 : mor cat carrier a) (pi2 : mor cat carrier b)
>                          (f : mor cat x a) (g : mor cat x b) where
>   constructor MkCommutingMorphism
>   challenger         : mor cat x carrier
>   commutativityLeft  : compose cat x carrier a challenger pi1 = f
>   commutativityRight : compose cat x carrier b challenger pi2 = g
>
> record Product (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkProduct
>   carrier : obj cat
>   pi1 : mor cat carrier a
>   pi2 : mor cat carrier b
>   exists : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b) -> CommutingMorphism cat x a b carrier pi1 pi2 f g
>   unique : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b)
>         -> (h : CommutingMorphism cat x a b carrier pi1 pi2 f g)
>         -> h = exists x f g
