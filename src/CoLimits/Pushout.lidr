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

> module CoLimits.Pushout
>
> import Basic.Category
> import CoLimits.CoLimit
> import CommutativeDiagram.Diagram
> import Data.Vect
> import Free.Graph
> import Free.PathCategory
>
> %access public export
> %default total
>
> data PushoutIndexObject = X | Y | Z
>
> PushoutIndexGraph : Graph
> PushoutIndexGraph = MkGraph
>   PushoutIndexObject
>   [(Z, X), (Z, Y)]
>
> PushoutIndexCategory : Category
> PushoutIndexCategory = pathCategory PushoutIndexGraph
>
> Pushout : {cat : Category} -> Diagram PushoutIndexCategory cat -> Type
> Pushout {cat} diagram = CoLimit PushoutIndexCategory cat diagram
