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

> module Span.Span
>
> import Basic.Category
> import Basic.Functor
> import CommutativeDiagram.Diagram
> import Data.Vect
> import Free.FreeFunctor
> import Free.Graph
> import Free.Path
> import Free.PathCategory
>
> %access public export
> %default total
>
> data SpanObject = X | Y | Z
>
> SpanGraph : Graph
> SpanGraph = MkGraph
>   SpanObject
>   [(Z, X), (Z, Y)]
>
> SpanIndexCategory : Category
> SpanIndexCategory = pathCategory SpanGraph
>
> Span : {cat : Category} -> (a, b : obj cat) -> Type
> Span {cat} a b = (d : Diagram SpanIndexCategory cat ** e : (mapObj d X = a) ** mapObj d Y = b)
>
> spanFunctor : {cat : Category} -> Span {cat} a b -> CFunctor SpanIndexCategory cat
> spanFunctor = fst
>
> span : {cat : Category}
>     -> (x, y, z : obj cat)
>     -> mor cat z x
>     -> mor cat z y
>     -> Span {cat} x y
> span {cat} x y z f g = (freeFunctor {cat} SpanGraph graphEmbedding ** Refl ** Refl)
>   where
>     geObj : SpanObject -> obj cat
>     geObj X = x
>     geObj Y = y
>     geObj Z = z
>
>     geMor : (i, j : SpanObject) -> Edge SpanGraph i j -> mor cat (geObj i) (geObj j)
>     geMor Z X Here         = f
>     geMor Z Y (There Here) = g
>     geMor X X Here         impossible
>     geMor X X (There Here) impossible
>     geMor X Y Here         impossible
>     geMor X Y (There Here) impossible
>     geMor X Z Here         impossible
>     geMor X Z (There Here) impossible
>     geMor Y X Here         impossible
>     geMor Y X (There Here) impossible
>     geMor Y Y Here         impossible
>     geMor Y Y (There Here) impossible
>     geMor Y Z Here         impossible
>     geMor Y Z (There Here) impossible
>     geMor Z X (There Here) impossible
>     geMor Z Y Here         impossible
>     geMor Z Z Here         impossible
>     geMor Z Z (There Here) impossible
>
>     graphEmbedding : GraphEmbedding SpanGraph cat
>     graphEmbedding = MkGraphEmbedding geObj geMor
