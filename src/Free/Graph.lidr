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

> module Free.Graph
>
> import Data.Vect
>
> %access public export
> %default total
>
> record Graph where
>   constructor MkGraph
>   vertices : Type
>   edges    : vertices -> vertices -> Type
>
> decidableFilter : DecEq a => (v : a) -> Vect n a -> (k ** Vect k (e ** e = v))
> decidableFilter v [] = (0 ** [])
> decidableFilter v (x :: xs) with (decEq x v)
>   decidableFilter v (x :: xs) | Yes prf = let (i ** vs) = decidableFilter v xs in (S i ** (x ** prf) :: vs)
>   decidableFilter v (x :: xs) | No cont = decidableFilter v xs
>
> edgeList : DecEq vertices
>         => (edges : Vect n (vertices, vertices))
>         -> Graph
> edgeList edges = MkGraph
>   vertices
>   (\v1, v2 => Fin $ DPair.fst $ decidableFilter (v1, v2) edges)
