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

> module CoLimits.CoCone
>
> import Basic.Category
>
> import Data.Graph
> import Data.Diagram
> import Data.Fin
>
> %access public export
> %default total
> %auto_implicits off
>
> record CoCone (cat : Category) (n : Nat) (m : Nat) (dia: Diagram cat n m) where
>   constructor MkCoCone
>   apex: obj cat
>   exists: (v : Fin n) -> mor cat (mapNodes dia v) apex
>   commutes:
>        (e : Fin m)
>     -> compose cat _ _ apex (mapEdges dia e) (exists (target (support dia) e))
>        = exists (source (support dia) e)
>
> record CoConeMorphism
>   (cat : Category)
>   (n : Nat) (m : Nat)
>   (dia : Diagram cat n m)
>   (source : CoCone cat n m dia)
>   (target : CoCone cat n m dia)
> where
>   constructor MkCoConeMorphism
>   carrier: mor cat (apex source) (apex target)
>   commutes:
>        (v : Fin n)
>     -> compose cat _ (apex source) (apex target) (exists source v) carrier
>        = (exists target v)
>
> postulate coConeMorphismEquality :
>      (cat : Category)
>   -> (n, m : Nat)
>   -> (dia : Diagram cat n m)
>   -> (a, b : CoCone cat n m dia)
>   -> (f : CoConeMorphism cat n m dia a b)
>   -> (g : CoConeMorphism cat n m dia a b)
>   -> (pf : carrier f = carrier g )
>   -> f = g
>
