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

> module Graph.Graph
>
> import Data.Vect
>
> %access public export
> %default total
>
> record Graph vertices where
>   constructor MkGraph
>   edges : Vect n (vertices, vertices)
>
> Edge : (graph : Graph vertices) -> (i, j : vertices) -> Type
> Edge g i j = Elem (i, j) (edges g)
>
> edgeOrigin : {graph : Graph vertices} -> Edge graph i j -> vertices
> edgeOrigin {i} _ = i
>
> edgeTarget : {graph : Graph vertices} -> Edge graph i j -> vertices
> edgeTarget {j} _ = j
>
> numEdges : Graph vertices -> Nat
> numEdges (MkGraph {n} _) = n
