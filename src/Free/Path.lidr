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

> module Free.Path
>
> import Data.List
> import Free.Graph
>
> %access public export
> %default total
>
> data Path : (g : Graph) -> vertices g -> vertices g -> Type where
>   Nil  : Path g i i
>   (::) : (a : Edge g i j) -> Path g j k -> Path g i k

nullPath : Path Graph.triangle One One
nullPath = Nil

oneToThree : Path Graph.triangle One Three
oneToThree = [Here, There Here]

oneToThree' : Path Graph.triangle One Three
oneToThree' = Here :: There Here :: Nil

> edgeToPath : {g : Graph} -> (a : Edge g i j) -> Path g (edgeOrigin a) (edgeTarget a)
> edgeToPath a = [a]
>
> joinPath : Path g i j -> Path g j k -> Path g i k
> joinPath [] y = y
> joinPath (x :: xs) y = x :: joinPath xs y
>
> joinPathNil : (p : Path g i j) -> joinPath p [] = p
> joinPathNil Nil       = Refl
> joinPathNil (x :: xs) = cong $ joinPathNil xs
>
> joinPathAssoc :
>      (p : Path g i j)
>   -> (q : Path g j k)
>   -> (r : Path g k l)
>   -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
> joinPathAssoc Nil q r = Refl
> joinPathAssoc (x :: xs) q r = cong $ joinPathAssoc xs q r
