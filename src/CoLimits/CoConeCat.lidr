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
>
> %access public export
> %default total
>
> identityCoCone :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (cocone : CoCone index cat dia)
>   -> CoConeMorphism index cat dia cocone cocone
> identityCoCone index cat dia cocone = MkCoConeMorphism
>   (identity cat (apex cocone))
>   (\i => rightIdentity cat (mapObj dia i) (apex cocone) (exists cocone i))
>
> composeCoCone :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (a, b, c : CoCone index cat dia)
>   -> (f : CoConeMorphism index cat dia a b)
>   -> (g : CoConeMorphism index cat dia b c)
>   -> CoConeMorphism index cat dia a c
> composeCoCone index cat dia a b c f g = MkCoConeMorphism
>   (compose cat (apex a) (apex b) (apex c) (carrier f) (carrier g))
>   (\i => let
>      leftCommutes = (commutes f) i
>      rightCommutes = (commutes g) i
>      makesRightCommutes = \x => compose cat (mapObj dia i) (apex b) (apex c) x (carrier g) = exists c i
>      leftMakesRightCommutes = replace {P = makesRightCommutes} (sym leftCommutes) rightCommutes
>      assoc = associativity cat (mapObj dia i) (apex a) (apex b) (apex c) (exists a i) (carrier f) (carrier g)
>    in trans assoc leftMakesRightCommutes)
>
> leftIdentityCoCone :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (a, b : CoCone index cat dia)
>   -> (f : CoConeMorphism index cat dia a b)
>   -> composeCoCone index cat dia a a b (identityCoCone index cat dia a) f = f
> leftIdentityCoCone index cat dia a b f = let
>    catLeftIdentity = leftIdentity cat (apex a) (apex b) (carrier f)
>    leftIdCompose = composeCoCone index cat dia a a b (identityCoCone index cat dia a) f
> in coConeMorphismEquality index cat dia a b leftIdCompose f catLeftIdentity
>
> rightIdentityCoCone :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (a, b : CoCone index cat dia)
>   -> (f : CoConeMorphism index cat dia a b)
>   -> composeCoCone index cat dia a b b f (identityCoCone index cat dia b) = f
> rightIdentityCoCone index cat dia a b f = let
>    catRightIdentity = rightIdentity cat (apex a) (apex b) (carrier f)
>    rightIdCompose = composeCoCone index cat dia a b b f (identityCoCone index cat dia b)
> in coConeMorphismEquality index cat dia a b rightIdCompose f catRightIdentity
>
> associativityCoCone :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (a, b, c, d : CoCone index cat dia)
>   -> (f : CoConeMorphism index cat dia a b)
>   -> (g : CoConeMorphism index cat dia b c)
>   -> (h: CoConeMorphism index cat dia c d)
>   -> composeCoCone index cat dia a b d f (composeCoCone index cat dia b c d g h)
>      = composeCoCone index cat dia a c d (composeCoCone index cat dia a b c f g) h
> associativityCoCone index cat dia a b c d f g h = let
>    catAssociativity = associativity cat (apex a) (apex b) (apex c) (apex d) (carrier f) (carrier g) (carrier h)
>    leftCompose = composeCoCone index cat dia a b d f (composeCoCone index cat dia b c d g h)
>    rightCompose = composeCoCone index cat dia a c d (composeCoCone index cat dia a b c f g) h
> in coConeMorphismEquality index cat dia a d leftCompose rightCompose catAssociativity
>
> CoConeCategory :
>      (index, cat : Category)
>   -> (dia: Diagram index cat)
>   -> Category
> CoConeCategory index cat dia = MkCategory
>   (CoCone index cat dia)
>   (CoConeMorphism index cat dia)
>   (identityCoCone index cat dia)
>   (composeCoCone index cat dia)
>   (leftIdentityCoCone index cat dia)
>   (rightIdentityCoCone index cat dia)
>   (associativityCoCone index cat dia)
>
