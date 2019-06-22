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
>
> import CoLimits.InitialObject
> import CoLimits.CoConeCat
> import CoLimits.CoCone
> import CoLimits.CoLimit
> import CommutativeDiagram.Diagram
> import Basic.Functor
>
> %access public export
> %default total
> %auto_implicits off
>
> emptyObject : Type
> emptyObject = Void
>
> emptyMorphism : Void -> Void -> Type
> emptyMorphism x y = Void
>
> empty : Category
> empty = MkCategory
>  (emptyObject)
>  (emptyMorphism)
>  (\a => absurd a)
>  (\a => absurd a)
>  (\a => absurd a)
>  (\a => absurd a)
>  (\a => absurd a)
>
> emptyMapObj : (cat : Category) -> obj empty -> obj cat
> emptyMapObj cat = void
>
> emptyMapMor :
>      (cat : Category)
>   -> (a, b : obj empty)
>   -> (f : mor empty a b)
>   -> mor cat (emptyMapObj cat a) (emptyMapObj cat b)
> emptyMapMor cat a b = void
>
> emptyDiagram : (cat: Category) -> Diagram empty cat
> emptyDiagram cat = MkCFunctor
>   (emptyMapObj cat)
>   (emptyMapMor cat)
>   (\a => absurd a)
>   (\a => absurd a)
>
> emptyCoCone :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> CoCone (emptyDiagram cat) (carrier io)
> emptyCoCone cat io = MkNaturalTransformation
>   (\i => absurd i)
>   (\i => absurd i)
>
> emptyDiagramCoLimitExists :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> (apexB : obj cat)
>  -> (b : CoCone (emptyDiagram cat) apexB)
>  -> CoConeMorphism empty cat (emptyDiagram cat) (carrier io) apexB (emptyCoCone cat io) b
> emptyDiagramCoLimitExists cat io apexB b = MkCoConeMorphism
>   (exists io apexB)
>   (\i => absurd i)
>
> emptyDiagramCoLimitIsUnique :
>     (cat : Category)
>  -> (io : InitialObject cat)
>  -> (apexB : obj cat)
>  -> (b : CoCone (emptyDiagram cat) apexB)
>  -> (f : CoConeMorphism empty cat (emptyDiagram cat) (carrier io) apexB (emptyCoCone cat io) b)
>  -> f = emptyDiagramCoLimitExists cat io apexB b
> emptyDiagramCoLimitIsUnique cat io apexB b f = let
>   coLimitMorphism = emptyDiagramCoLimitExists cat io apexB b
>   apexMorphismUniqueness = unique io apexB (apexMorphism f) (apexMorphism coLimitMorphism)
> in coConeMorphismEquality f coLimitMorphism apexMorphismUniqueness
>
> initialObjectToCoLimit :
>      (cat  : Category)
>   -> (io : InitialObject cat)
>   -> CoLimit empty cat (emptyDiagram cat)
> initialObjectToCoLimit cat io = MkCoLimit
>   (carrier io)
>   (emptyCoCone cat io)
>   (emptyDiagramCoLimitExists cat io)
>   (emptyDiagramCoLimitIsUnique cat io)
