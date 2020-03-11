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
> import Basic.DiagonalFunctor
> import Basic.Functor
> import Basic.NaturalTransformation
>
> %access public export
> %default total
> %auto_implicits off
>
> CoCone :
>      {index, cat : Category}
>   -> (diagram : Diagram index cat)
>   -> (n : obj cat)
>   -> Type
> CoCone {index} {cat} diagram n = NaturalTransformation index cat diagram (Delta index cat n)
>
> record CoConeMorphism
>   (index : Category) (cat : Category)
>   (diagram : Diagram index cat)
>   (a: obj cat) (b : obj cat)
>   (source : CoCone diagram a) (target : CoCone diagram b)
> where
>   constructor MkCoConeMorphism
>   apexMorphism   : mor cat a b
>   commutativity : (i : obj index)
>                -> compose cat _ a b (component source i) apexMorphism
>                 = (component target i)
>
> postulate coConeMorphismEquality :
>      {index, cat : Category}
>   -> {diagram : Diagram index cat}
>   -> {a, b : obj cat}
>   -> {source : CoCone diagram a}
>   -> {target : CoCone diagram b}
>   -> (f, g : CoConeMorphism index cat diagram a b source target)
>   -> apexMorphism f = apexMorphism g
>   -> f = g
