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

> module CoLimits.CoConeCat
>
> import Basic.Category
>
> import CoLimits.CoCone
> import CommutativeDiagram.Diagram
> import Basic.Functor
> import Basic.NaturalTransformation
>
> %access public export
> %default total
> %auto_implicits off
>
> identityCoCone :
>      {index, cat : Category}
>   -> {dia : Diagram index cat}
>   -> {apex : obj cat}
>   -> (cocone : CoCone dia apex)
>   -> CoConeMorphism index cat dia apex apex cocone cocone
> identityCoCone {cat} {dia} {apex} cocone = MkCoConeMorphism
>   (identity cat apex)
>   (\i => rightIdentity cat (mapObj dia i) apex (component cocone i))
>
> composeCoCone :
>      {index, cat : Category}
>   -> {dia : Diagram index cat}
>   -> {apexA, apexB, apexC : obj cat}
>   -> (a : CoCone dia apexA)
>   -> (b : CoCone dia apexB)
>   -> (c : CoCone dia apexC)
>   -> (f : CoConeMorphism index cat dia apexA apexB a b)
>   -> (g : CoConeMorphism index cat dia apexB apexC b c)
>   -> CoConeMorphism index cat dia apexA apexC a c
> composeCoCone {cat} {dia} a b c f g = MkCoConeMorphism
>   (compose cat apexA apexB apexC (apexMorphism f) (apexMorphism g))
>   (\i => let
>      leftCommutes = (commutativity f) i
>      rightCommutes = (commutativity g) i
>      makesRightCommute = \x => compose cat (mapObj dia i) apexB apexC x (apexMorphism g) = component c i
>      leftMakesRightCommute = replace {P = makesRightCommute} (sym leftCommutes) rightCommutes
>      assoc = associativity cat (mapObj dia i) apexA apexB apexC (component a i) (apexMorphism f) (apexMorphism g)
>    in trans assoc leftMakesRightCommute)
>
> leftIdentityCoCone :
>      {index, cat : Category}
>   -> {dia : Diagram index cat}
>   -> {apexA, apexB : obj cat}
>   -> (a : CoCone dia apexA)
>   -> (b : CoCone dia apexB)
>   -> (f : CoConeMorphism index cat dia apexA apexB a b)
>   -> composeCoCone a a b (identityCoCone a) f = f
> leftIdentityCoCone {cat} {dia} {apexA} {apexB} a b f = let
>    catLeftIdentity = leftIdentity cat apexA apexB (apexMorphism f)
>    leftIdCompose = composeCoCone a a b (identityCoCone a) f
> in coConeMorphismEquality leftIdCompose f catLeftIdentity
>
> rightIdentityCoCone :
>      {index, cat : Category}
>   -> {dia : Diagram index cat}
>   -> {apexA, apexB : obj cat}
>   -> (a : CoCone dia apexA)
>   -> (b : CoCone dia apexB)
>   -> (f : CoConeMorphism index cat dia apexA apexB a b)
>   -> composeCoCone a b b f (identityCoCone b) = f
> rightIdentityCoCone {cat} {dia} {apexA} {apexB} a b f = let
>    catRightIdentity = rightIdentity cat apexA apexB (apexMorphism f)
>    rightIdCompose = composeCoCone a b b f (identityCoCone b)
> in coConeMorphismEquality rightIdCompose f catRightIdentity
>
> associativityCoCone :
>      {index, cat : Category}
>   -> {dia : Diagram index cat}
>   -> {apexA, apexB, apexC, apexD : obj cat}
>   -> (a : CoCone dia apexA)
>   -> (b : CoCone dia apexB)
>   -> (c : CoCone dia apexC)
>   -> (d : CoCone dia apexD)
>   -> (f : CoConeMorphism index cat dia apexA apexB a b)
>   -> (g : CoConeMorphism index cat dia apexB apexC b c)
>   -> (h: CoConeMorphism index cat dia apexC apexD c d)
>   -> composeCoCone a b d f (composeCoCone b c d g h)
>      = composeCoCone a c d (composeCoCone a b c f g) h
> associativityCoCone {cat} {dia} {apexA} {apexB} {apexC} {apexD} a b c d f g h = let
>    catAssociativity = associativity cat apexA apexB apexC apexD (apexMorphism f) (apexMorphism g) (apexMorphism h)
>    leftCompose = composeCoCone a b d f (composeCoCone b c d g h)
>    rightCompose = composeCoCone a c d (composeCoCone a b c f g) h
> in coConeMorphismEquality leftCompose rightCompose catAssociativity
>
> record CoConeObject
>   (index : Category)
>   (cat : Category)
>   (dia : Diagram index cat)
> where
>  constructor MkCoConeObject
>  apex : obj cat
>  cocone : CoCone dia apex
>
> -- We can define a CoCone category as a comma category
> -- @see https://en.wikipedia.org/wiki/Cone_(category_theory)#equivalent-formulations
> CoConeCategory :
>      (index, cat : Category)
>   -> (dia: Diagram index cat)
>   -> Category
> CoConeCategory index cat dia = MkCategory
>   (CoConeObject index cat dia)
>   (\a, b => CoConeMorphism index cat dia (apex a) (apex b) (cocone a) (cocone b))
>   (\a => identityCoCone (cocone a))
>   (\a, b, c, f, g => composeCoCone (cocone a) (cocone b) (cocone c) f g)
>   (\a, b, f => leftIdentityCoCone (cocone a) (cocone b) f)
>   (\a, b, f => rightIdentityCoCone (cocone a) (cocone b) f)
>   (\a, b, c, d, f, g, h => associativityCoCone (cocone a) (cocone b) (cocone c) (cocone d) f g h)
>
