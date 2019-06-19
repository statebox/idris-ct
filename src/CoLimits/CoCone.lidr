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
> import CommutativeDiagram.Diagram
> import Basic.Functor
>
> %access public export
> %default total
>
> record CoCone (index : Category) (cat : Category) (dia : Diagram index cat) where
>   constructor MkCoCone
>   apex: obj cat
>   exists: (j : obj index) -> mor cat (mapObj dia j) apex
>   commutes:
>        (i, j : obj index)
>     -> (f : mor index i j)
>     -> compose cat (mapObj dia i) (mapObj dia j) apex (mapMor dia i j f) (exists j)
>        = exists i
>
> record CoConeMorphism
>   (index : Category) (cat : Category)
>   (dia : Diagram index cat)
>   (source : CoCone index cat dia)
>   (target : CoCone index cat dia)
> where
>   constructor MkCoConeMorphism
>   carrier: mor cat (apex source) (apex target)
>   commutes:
>        (i : obj index)
>     -> compose cat _ (apex source) (apex target) (exists source i) carrier
>        = (exists target i)
>
> postulate coConeMorphismEquality :
>      (index : Category)
>   -> (cat : Category)
>   -> (dia : Diagram index cat)
>   -> (a, b : CoCone index cat dia)
>   -> (f : CoConeMorphism index cat dia a b)
>   -> (g : CoConeMorphism index cat dia a b)
>   -> (pf : carrier f = carrier g )
>   -> f = g
>
