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
> import Data.List
>
> %access public export
> %default total
>
> record Graph where
>   constructor MkGraph
>   vertices : Type
>   edges    : List (vertices, vertices)
>
> Edge : (g : Graph) -> (i, j : vertices g) -> Type
> Edge (MkGraph _ e) v1 v2 = Elem (v1, v2) e
>
> edgeOrigin : {g : Graph} -> Edge g i j -> vertices g
> edgeOrigin {i} _ = i
>
> edgeTarget : {g : Graph} -> Edge g i j -> vertices g
> edgeTarget {j} _ = j

data TriangleVertices = One | Two | Three

triangle : Graph
triangle = MkGraph TriangleVertices [(One, Two), (Two, Three), (Three, One)]
