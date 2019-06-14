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

> module CoLimits.InitialObjectAsCoLimit
>
> import Basic.Category
>
> import Data.Graph
> import Data.Diagram
> import Data.Fin
>
> import CoLimits.InitialObject
> import CoLimits.CoConeCat
> import CoLimits.CoCone
> import CoLimits.CoLimit
>
> %access public export
> %default total
>
> nil : Fin Z -> _
> nil x impossible
>
> emptyGraph : Graph Z Z
> emptyGraph = MkGraph nil nil
>
> emptyDiagram : (cat: Category) -> Diagram cat Z Z
> emptyDiagram cat = MkDiagram emptyGraph nil (\e => absurd e)
>
> emptyCoConeExists :
>      (cat : Category)
>   -> (io : InitialObject cat)
>   -> (v : Fin Z)
>   -> mor cat (mapNodes (emptyDiagram cat) v) (carrier io)
> emptyCoConeExists cat io v impossible
>
> emptyCoConeCommutes :
>      (cat : Category)
>   -> (io : InitialObject cat)
>   -> (e : Fin Z)
>   -> compose cat _ _ (carrier io)
>        (mapEdges (emptyDiagram cat) e) (emptyCoConeExists cat io (target (support (emptyDiagram cat)) e))
>      = emptyCoConeExists cat io (source (support (emptyDiagram cat)) e)
> emptyCoConeCommutes cat io e impossible
>
> emptyCoCone :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> CoCone cat Z Z (emptyDiagram cat)
> emptyCoCone cat io = MkCoCone
>   (carrier io)
>   (emptyCoConeExists cat io)
>   (emptyCoConeCommutes cat io)
>
> emptyDiagramCoLimitExists :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> (b : CoCone cat Z Z (emptyDiagram cat))
>  -> CoConeMorphism cat Z Z (emptyDiagram cat) (emptyCoCone cat io) b
> emptyDiagramCoLimitExists cat io b = MkCoConeMorphism
>   (exists io (apex b))
>   (\v => absurd v)
>
> emptyDiagramCoLimitIsUnique :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> (b : CoCone cat Z Z (emptyDiagram cat))
>  -> (f : CoConeMorphism cat Z Z (emptyDiagram cat) (emptyCoCone cat io) b)
>  -> f = emptyDiagramCoLimitExists cat io b
> emptyDiagramCoLimitIsUnique cat io b f = let
>   exists = emptyDiagramCoLimitExists cat io b
>   pf = unique io (apex b) (carrier f) (carrier exists)
> in coConeMorphismEquality cat Z Z (emptyDiagram cat) (emptyCoCone cat io) b f exists pf
>
> initialObjectToCoLimit :
>      (cat  : Category)
>   -> (io : InitialObject cat)
>   -> CoLimit cat Z Z (emptyDiagram cat)
> initialObjectToCoLimit cat io = MkCoLimit
>   (emptyCoCone cat io)
>   (emptyDiagramCoLimitExists cat io)
>   (emptyDiagramCoLimitIsUnique cat io)
