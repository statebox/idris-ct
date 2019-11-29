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

> module Graph.FreeFunctor
>
> import Basic.Category
> import Basic.Functor
> import Data.Vect
> import Graph.Graph
> import Graph.Path
> import Graph.PathCategory
>
> %access public export
> %default total
>
> record GraphEmbedding (vertices : Type) (g : Graph vertices) (cat : Category) where
>   constructor MkGraphEmbedding
>   mapVertices : vertices -> obj cat
>   mapEdges    : (i, j : vertices) -> Edge {vertices} g i j -> mor cat (mapVertices i) (mapVertices j)
>
> foldPath :
>      (graph : Graph vertices)
>   -> (graphEmbedding : GraphEmbedding vertices graph cat)
>   -> Path graph i j
>   -> mor cat (mapVertices graphEmbedding i) (mapVertices graphEmbedding j)
> foldPath _     {cat} graphEmbedding {i} []              = identity cat (mapVertices graphEmbedding i)
> foldPath graph {cat} graphEmbedding {i} ((::) {j} x xs) = compose cat _ _ _ (mapEdges graphEmbedding i j x)
>                                                                             (foldPath graph graphEmbedding xs)
>
> freeFunctorCompose :
>      (graph : Graph vertices)
>   -> (graphEmbedding : GraphEmbedding vertices graph cat)
>   -> (i, j, k : vertices)
>   -> (f : Path graph i j)
>   -> (h : Path graph j k)
>   -> foldPath graph graphEmbedding {i} {j = k} (joinPath f h)
>    = compose cat
>              (mapVertices graphEmbedding i)
>              (mapVertices graphEmbedding j)
>              (mapVertices graphEmbedding k)
>              (foldPath graph graphEmbedding {i} {j} f)
>              (foldPath graph graphEmbedding {i = j} {j = k} h)
> freeFunctorCompose graph {cat} graphEmbedding j j k [] h = sym $
>   leftIdentity cat (mapVertices graphEmbedding j) (mapVertices graphEmbedding k) (foldPath graph graphEmbedding h)
> freeFunctorCompose graph {cat} graphEmbedding i j k ((::) {j=l} x xs) h =
>   trans (cong {f = compose cat _ _ _ (mapEdges graphEmbedding i l x)}
>               (freeFunctorCompose graph graphEmbedding _ _ _ xs h))
>         (associativity cat _ _ _ _ (mapEdges graphEmbedding i l x)
>                                    (foldPath graph graphEmbedding xs)
>                                    (foldPath graph graphEmbedding h))
>
> freeFunctor : (graph : Graph vertices) -> GraphEmbedding vertices graph cat -> CFunctor (pathCategory graph) cat
> freeFunctor graph graphEmbedding = MkCFunctor
>   (mapVertices graphEmbedding)
>   (\i, j, p => foldPath graph graphEmbedding {i} {j} p)
>   (\_ => Refl)
>   (freeFunctorCompose graph graphEmbedding)
