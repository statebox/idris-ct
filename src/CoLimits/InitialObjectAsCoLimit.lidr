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
> import Basic.Functor
> import Basic.NaturalTransformation
> import CoLimits.CoCone
> import CoLimits.CoConeCat
> import CoLimits.CoLimit
> import CoLimits.InitialObject
> import CommutativeDiagram.Diagram
> import Empty.EmptyCategory
> import Empty.EmptyFunctor
>
> %access public export
> %default total
> %auto_implicits off
>
> emptyDiagram : (cat : Category) -> Diagram emptyCategory cat
> emptyDiagram = emptyFunctor
>
> emptyCoCone :
>     (cat : Category)
>  -> (initial : InitialObject cat)
>  -> CoCone (emptyDiagram cat) (carrier initial)
> emptyCoCone cat initial = MkNaturalTransformation
>   (\i => absurd i)
>   (\i => absurd i)
>
> emptyDiagramCoLimitExists :
>     (cat : Category)
>  -> (initial : InitialObject cat)
>  -> (apexB : obj cat)
>  -> (b : CoCone (emptyDiagram cat) apexB)
>  -> CoConeMorphism emptyCategory cat (emptyDiagram cat) (carrier initial) apexB (emptyCoCone cat initial) b
> emptyDiagramCoLimitExists cat initial apexB b = MkCoConeMorphism
>   (exists initial apexB)
>   (\i => absurd i)
>
> emptyDiagramCoLimitIsUnique :
>     (cat : Category)
>  -> (initial : InitialObject cat)
>  -> (apexB : obj cat)
>  -> (b : CoCone (emptyDiagram cat) apexB)
>  -> (f, g : CoConeMorphism emptyCategory cat (emptyDiagram cat) (carrier initial) apexB (emptyCoCone cat initial) b)
>  -> f = g
> emptyDiagramCoLimitIsUnique cat initial apexB b f g = let
>   apexMorphismUniqueness = unique initial apexB (apexMorphism f) (apexMorphism g)
> in coConeMorphismEquality f g apexMorphismUniqueness
>
> initialObjectToCoLimit :
>      (cat  : Category)
>   -> (initial : InitialObject cat)
>   -> CoLimit emptyCategory cat (emptyDiagram cat)
> initialObjectToCoLimit cat initial = MkCoLimit
>   (carrier initial)
>   (emptyCoCone cat initial)
>   (emptyDiagramCoLimitExists cat initial)
>   (emptyDiagramCoLimitIsUnique cat initial)
