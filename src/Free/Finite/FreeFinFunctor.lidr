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

> module Free.Finite.FreeFinFunctor
>
> import Basic.Category
> import Basic.Functor
> import Data.Vect
> import Free.Finite.FinGraph
> import Free.Finite.FinPath
> import Free.Finite.FinPathCategory
>
> %access public export
> %default total
>
> record FinGraphEmbedding (g : FinGraph) (cat : Category) where
>   constructor MkFinGraphEmbedding
>   mapVertices : vertices g -> obj cat
>   mapEdges    : (i, j : vertices g) -> Edge g i j -> mor cat (mapVertices i) (mapVertices j)
>
> foldFinPath :
>      (g : FinGraph)
>   -> (ge : FinGraphEmbedding g cat)
>   -> FinPath g i j
>   -> mor cat (mapVertices ge i) (mapVertices ge j)
> foldFinPath _ {cat} ge {i} []              = identity cat (mapVertices ge i)
> foldFinPath g {cat} ge {i} ((::) {j} x xs) = compose cat _ _ _ (mapEdges ge i j x) (foldFinPath g ge xs)
>
> freeFinFunctorCompose :
>      (g : FinGraph)
>   -> (ge : FinGraphEmbedding g cat)
>   -> (i, j, k : vertices g)
>   -> (f : FinPath g i j)
>   -> (h : FinPath g j k)
>   -> foldFinPath g ge {i} {j = k} (joinFinPath f h)
>    = compose cat
>              (mapVertices ge i)
>              (mapVertices ge j)
>              (mapVertices ge k)
>              (foldFinPath g ge {i} {j} f)
>              (foldFinPath g ge {i = j} {j = k} h)
> freeFinFunctorCompose g {cat} ge j j k [] h = sym $ leftIdentity cat
>                                                               (mapVertices ge j)
>                                                               (mapVertices ge k)
>                                                               (foldFinPath g ge h)
> freeFinFunctorCompose g {cat} ge i j k ((::) {j=l} x xs) h =
>   trans (cong {f = compose cat _ _ _ (mapEdges ge i l x)} $ freeFinFunctorCompose g ge _ _ _ xs h)
>         (associativity cat _ _ _ _ (mapEdges ge i l x) (foldFinPath g ge xs) (foldFinPath g ge h))
>
> freeFinFunctor : (g : FinGraph) -> FinGraphEmbedding g cat -> CFunctor (pathCategory g) cat
> freeFinFunctor g ge = MkCFunctor
>   (mapVertices ge)
>   (\i, j, p => foldFinPath g ge {i} {j} p)
>   (\_ => Refl)
>   (freeFinFunctorCompose g ge)
