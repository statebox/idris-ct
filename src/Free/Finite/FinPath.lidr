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

> module Free.Finite.FinPath
>
> import Data.List
> import Free.Finite.FinGraph
>
> %access public export
> %default total
>
> data FinPath : (g : FinGraph) -> vertices g -> vertices g -> Type where
>   Nil  : FinPath g i i
>   (::) : (a : Edge g i j) -> FinPath g j k -> FinPath g i k

nullFinPath : FinPath FinGraph.triangle One One
nullFinPath = Nil

oneToThree : FinPath FinGraph.triangle One Three
oneToThree = [Here, There Here]

oneToThree' : FinPath FinGraph.triangle One Three
oneToThree' = Here :: There Here :: Nil

> edgeToFinPath : {g : FinGraph} -> (a : Edge g i j) -> FinPath g (edgeOrigin a) (edgeTarget a)
> edgeToFinPath a = [a]
>
> joinFinPath : FinPath g i j -> FinPath g j k -> FinPath g i k
> joinFinPath [] y = y
> joinFinPath (x :: xs) y = x :: joinFinPath xs y
>
> joinFinPathNil : (p : FinPath g i j) -> joinFinPath p [] = p
> joinFinPathNil Nil       = Refl
> joinFinPathNil (x :: xs) = cong $ joinFinPathNil xs
>
> joinFinPathAssoc :
>      (p : FinPath g i j)
>   -> (q : FinPath g j k)
>   -> (r : FinPath g k l)
>   -> joinFinPath p (joinFinPath q r) = joinFinPath (joinFinPath p q) r
> joinFinPathAssoc Nil q r = Refl
> joinFinPathAssoc (x :: xs) q r = cong $ joinFinPathAssoc xs q r
