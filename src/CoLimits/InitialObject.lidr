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

> module CoLimits.InitialObject
>
> import Basic.Category
> import Basic.Isomorphism
>
> %access public export
> %default total
> %auto_implicits off
>
> record InitialObject (cat : Category) where
>   constructor MkInitialObject
>   carrier : obj cat
>   exists  : (b : obj cat) -> mor cat carrier b
>   unique  : (b : obj cat) -> (f, g : mor cat carrier b) -> f = g
>
> composeInitialMorphisms :
>      (cat : Category)
>   -> (a, b : InitialObject cat)
>   -> mor cat (carrier a) (carrier a)
> composeInitialMorphisms cat a b =
>   let
>     x = carrier a
>     y = carrier b
>   in
>     compose cat x y x (exists a y) (exists b x)
>
> initialObjectsAreIsomorphic :
>      (cat : Category)
>   -> (a, b : InitialObject cat)
>   -> Isomorphic cat (carrier a) (carrier b)
> initialObjectsAreIsomorphic cat a b = buildIsomorphic
>   (exists a (carrier b))
>   (exists b (carrier a))
>   (unique a (carrier a) (composeInitialMorphisms cat a b) (identity cat (carrier a)))
>   (unique b (carrier b) (composeInitialMorphisms cat b a) (identity cat (carrier b)))
