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

> module Preorder.PreorderAsCategory
>
> import Basic.Category
> import Preorder.UniquePreorder
>
> -- contrib
> import Decidable.Order
>
> %access public export
> %default total
>
> leftIdentity : UniquePreorder t po
>   => (a, b : t)
>   -> (f : po a b)
>   -> transitive a a b (reflexive a) f = f
> leftIdentity a b f = unique a b (transitive a a b (reflexive a) f) f
>
> rightIdentity : UniquePreorder t po
>   => (a, b : t)
>   -> (f : po a b)
>   -> transitive a b b f (reflexive b) = f
> rightIdentity a b f = unique a b (transitive a b b f (reflexive b)) f
>
> associativity : UniquePreorder t po
>   => (a, b, c, d : t)
>   -> (f : po a b)
>   -> (g : po b c)
>   -> (h : po c d)
>   -> transitive a b d f (transitive b c d g h) = transitive a c d (transitive a b c f g) h
> associativity a b c d f g h = unique a d
>   (Decidable.Order.transitive a b d f (transitive b c d g h))
>   (Decidable.Order.transitive a c d (transitive a b c f g) h)
>
> preorderAsCategory : UniquePreorder t po => Category
> preorderAsCategory {t} {po} = MkCategory
>   t
>   po
>   reflexive
>   transitive
>   (leftIdentity {t} {po})
>   (rightIdentity {t} {po})
>   (associativity {t} {po})
