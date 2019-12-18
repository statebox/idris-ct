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

> module Graph.Path
>
> import Data.List
> import Data.Vect
> import Graph.Graph
>
> %access public export
> %default total
>
> data Path : (graph : Graph vertices) -> vertices -> vertices -> Type where
>   Nil  : Path graph i i
>   (::) : (a : Edge graph i j) -> Path graph j k -> Path graph i k
>
> Show (Path graph i j) where
>   show [] = ""
>   show (x :: xs) = show x ++ "," ++ show xs
>
> edgeToPath : {graph : Graph vertices} -> (a : Edge graph i j) -> Path graph (edgeOrigin a) (edgeTarget a)
> edgeToPath a = [a]
>
> joinPath : Path graph i j -> Path graph j k -> Path graph i k
> joinPath [] y = y
> joinPath (x :: xs) y = x :: joinPath xs y
>
> joinPathNil : (p : Path g i j) -> joinPath p [] = p
> joinPathNil Nil       = Refl
> joinPathNil (x :: xs) = cong $ joinPathNil xs
>
> joinPathAssoc :
>      (p : Path graph i j)
>   -> (q : Path graph j k)
>   -> (r : Path graph k l)
>   -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
> joinPathAssoc Nil q r = Refl
> joinPathAssoc (x :: xs) q r = cong $ joinPathAssoc xs q r
