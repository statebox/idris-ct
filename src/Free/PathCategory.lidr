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

> module Free.PathCategory
>
> import Basic.Category
> import Free.Graph
>
> %access public export
> %default total
>
> ||| IDRIS MAGIC a :: b :: c :: Nil = [a,b,c]
> data Path : (e : t -> t -> Type) -> t -> t -> Type where
>   Nil  : Path e i i
>   (::) : e i j -> Path e j k -> Path e i k
>
> edgeToPath : {g : Graph v} -> Edge g i j -> Path (Edge g) i j
> edgeToPath e = [e]
>
> joinPath : {e : t -> t -> Type} -> Path e i j -> Path e j k -> Path e i k
> joinPath []        y = y
> joinPath (x :: xs) y = x :: joinPath xs y
>
> joinPathNil : (p : Path e i j) -> joinPath p [] = p
> joinPathNil Nil        = Refl
> joinPathNil (eij :: p) = cong $ joinPathNil p
>
> joinPathAssoc :
>      (p : Path e i j)
>   -> (q : Path e j k)
>   -> (r : Path e k l)
>   -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
> joinPathAssoc Nil q r        = Refl
> joinPathAssoc (eij :: p) q r = cong $ joinPathAssoc p q r
>
> pathCategory : Graph v -> Category
> pathCategory (MkGraph e) = MkCategory
>   v
>   (Path e)
>   (\a => Nil)
>   (\a, b, c, f, g => joinPath f g)
>   (\a, b, f => Refl)
>   (\a, b, f => joinPathNil f)
>   (\a, b, c, d, f, g, h => joinPathAssoc f g h)
