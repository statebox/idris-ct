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

> module FAlgebras.FAlgebraHomomorphism
>
> import Basic.Category
> import Basic.Functor
> import FAlgebras.FAlgebra
>
> %access public export
> %default total
>
> record FAlgebraHomomorphism
>   (cat : Category)
>   (func : CFunctor cat cat)
>   (domain : FAlgebra cat func)
>   (codomain : FAlgebra cat func)
>   where
>     constructor MkFAlgebraHomomorphism
>     morphism  : mor cat (carrier domain) (carrier codomain)
>     coherence : compose cat (mapObj func (carrier domain))
>                             (carrier domain)
>                             (carrier codomain)
>                             (evaluation domain)
>                             morphism
>               = compose cat (mapObj func (carrier domain))
>                             (mapObj func (carrier codomain))
>                             (carrier codomain)
>                             (mapMor func (carrier domain) (carrier codomain) morphism)
>                             (evaluation codomain)
