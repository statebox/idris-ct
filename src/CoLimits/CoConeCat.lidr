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
> import Data.Graph
> import Data.Diagram
> import Data.Fin
> import CoLimits.CoCone
>
> %access public export
> %default total
>
> identityCoCone :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (cocone : CoCone cat n m dia)
>   -> CoConeMorphism cat n m dia cocone cocone
> identityCoCone cat n m dia cocone = MkCoConeMorphism
>   (identity cat (apex cocone))
>   (\v => rightIdentity cat (mapNodes dia v) (apex cocone) (exists cocone v))
>
> composeCoCone :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (a, b, c : CoCone cat n m dia)
>   -> (f : CoConeMorphism cat n m dia a b)
>   -> (g : CoConeMorphism cat n m dia b c)
>   -> CoConeMorphism cat n m dia a c
> composeCoCone cat n m dia a b c f g = MkCoConeMorphism
>   (compose cat (apex a) (apex b) (apex c) (carrier f) (carrier g))
>   (\v => let
>      leftCommutes = (commutes f) v
>      rightCommutes = (commutes g) v
>      makesRightCommutes = \x => compose cat (mapNodes dia v) (apex b) (apex c) x (carrier g) = exists c v
>      leftMakesRightCommutes = replace {P = makesRightCommutes} (sym leftCommutes) rightCommutes
>      assoc = associativity cat (mapNodes dia v) (apex a) (apex b) (apex c) (exists a v) (carrier f) (carrier g)
>    in trans assoc leftMakesRightCommutes)
>
> leftIdentityCoCone :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (a, b : CoCone cat n m dia)
>   -> (f : CoConeMorphism cat n m dia a b)
>   -> composeCoCone cat n m dia a a b (identityCoCone cat n m dia a) f = f
> leftIdentityCoCone cat n m dia a b f = let
>    catLeftIdentity = leftIdentity cat (apex a) (apex b) (carrier f)
>    leftIdCompose = composeCoCone cat n m dia a a b (identityCoCone cat n m dia a) f
> in coConeMorphismEquality cat n m dia a b leftIdCompose f catLeftIdentity
>
> rightIdentityCoCone :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (a, b : CoCone cat n m dia)
>   -> (f : CoConeMorphism cat n m dia a b)
>   -> composeCoCone cat n m dia a b b f (identityCoCone cat n m dia b) = f
> rightIdentityCoCone cat n m dia a b f = let
>    catRightIdentity = rightIdentity cat (apex a) (apex b) (carrier f)
>    rightIdCompose = composeCoCone cat n m dia a b b f (identityCoCone cat n m dia b)
> in coConeMorphismEquality cat n m dia a b rightIdCompose f catRightIdentity
>
> associativityCoCone :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (a, b, c, d : CoCone cat n m dia)
>   -> (f : CoConeMorphism cat n m dia a b)
>   -> (g : CoConeMorphism cat n m dia b c)
>   -> (h: CoConeMorphism cat n m dia c d)
>   -> composeCoCone cat n m dia a b d f (composeCoCone cat n m dia b c d g h)
>      = composeCoCone cat n m dia a c d (composeCoCone cat n m dia a b c f g) h
> associativityCoCone cat n m dia a b c d f g h = let
>    catAssociativity = associativity cat (apex a) (apex b) (apex c) (apex d) (carrier f) (carrier g) (carrier h)
>    leftCompose = composeCoCone cat n m dia a b d f (composeCoCone cat n m dia b c d g h)
>    rightCompose = composeCoCone cat n m dia a c d (composeCoCone cat n m dia a b c f g) h
> in coConeMorphismEquality cat n m dia a d leftCompose rightCompose catAssociativity
>
> CoConeCategory :
>      (cat : Category)
>   -> (n : Nat)
>   -> (m : Nat)
>   -> (dia: Diagram cat n m)
>   -> Category
> CoConeCategory cat n m dia = MkCategory
>   (CoCone cat n m dia)
>   (CoConeMorphism cat n m dia)
>   (identityCoCone cat n m dia)
>   (composeCoCone cat n m dia)
>   (leftIdentityCoCone cat n m dia)
>   (rightIdentityCoCone cat n m dia)
>   (associativityCoCone cat n m dia)
>
