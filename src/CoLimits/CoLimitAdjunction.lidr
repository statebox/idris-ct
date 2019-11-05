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

> module CoLimits.CoLimitAdjunction
>
> import Basic.Adjunction
> import Basic.Category
> import Basic.ConstantFunctor
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Cats.FunctorsAsCategory
> import CoLimits.CoCone
> import CoLimits.CoLimit
> import CommutativeDiagram.Diagram
> import Idris.TypesAsCategoryExtensional as Idris
>
> homIsoLawLeft : {index, cat : Category} -> {diagram : Diagram index cat} -> (colimit : CoLimit index cat diagram) -> (b : obj cat)
>   -> (f : mor cat (carrier colimit) b) -> apexMorphism (exists colimit b (naturalTransformationComposition _ _ _ _ _ (cocone colimit) (mapMor (DiagonalFunctor index cat) (carrier colimit) b f))) = f
> homIsoLawLeft colimit b f = ?w1
>
> homIsoLawRight : {index, cat : Category} -> {diagram : Diagram index cat} -> (colimit : CoLimit index cat diagram) -> (b : obj cat)
>   -> (coconeB : CoCone diagram b) -> naturalTransformationComposition _ _ _ _ _ (cocone colimit) (mapMor (DiagonalFunctor index cat) (carrier colimit) b (apexMorphism (exists colimit b coconeB))) = coconeB
> homIsoLawRight colimit b coconeB = naturalTransformationExt _ _ _ _ _ _ (\a => commutativity (exists colimit b coconeB) a)
>
> homIso : {index, cat : Category} -> {diagram : Diagram index cat} -> (colimit : CoLimit index cat diagram) -> (b : obj cat)
>   -> Isomorphism Idris.typesAsCategoryExtensional (mor cat (carrier colimit) b) (NaturalTransformation index cat diagram (Delta index cat b))
> homIso {index} {cat} {diagram} colimit b = MkIsomorphism
>   (MkExtensionalTypeMorphism (\h => naturalTransformationComposition index cat diagram (Delta index cat (carrier colimit)) (Delta index cat b) (cocone colimit) (mapMor (DiagonalFunctor index cat) _ _ h)))
>   (MkExtensionalTypeMorphism (\n => apexMorphism (exists colimit b n)))
>   (funExt (homIsoLawLeft colimit b))
>   (funExt (homIsoLawRight colimit b))
>
> colimitAdjunction : (index, cat : Category)
>                  -> (colimitsExist : (diagram : Diagram index cat) -> CoLimit index cat diagram)
>                  -> Adjunction cat (functorCategory index cat)
>                       (colimitFunctor index cat colimitsExist)
>                       (DiagonalFunctor index cat)
> colimitAdjunction index cat colimitsExist = MkAdjunction
>   (\diagram, b => homIso (colimitsExist diagram) b)
>   (\f, g, h => ?comm)
