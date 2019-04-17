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

> module Idris.FunctorAsCFunctor
>
> import Basic.Category
> import Basic.Functor
> import Idris.TypesAsCategoryExtensional
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> functorOnMorphisms :
>      VerifiedFunctor f
>   -> (a, b : Type)
>   -> ExtensionalTypeMorphism a b
>   -> ExtensionalTypeMorphism (f a) (f b)
> functorOnMorphisms _ _ _ (MkExtensionalTypeMorphism g) = MkExtensionalTypeMorphism (map g)
>
> functorPreserveId :
>      (func : VerifiedFunctor f)
>   -> (a : Type)
>   -> functorOnMorphisms func a a (extIdentity a) = extIdentity (f a)
> functorPreserveId _ a = funExt (\x => functorIdentity {a} id (\v => Refl) x)
>
> functorPreserveCompose :
>      (func : VerifiedFunctor f)
>   -> (a, b, c : Type)
>   -> (g : ExtensionalTypeMorphism a b)
>   -> (h : ExtensionalTypeMorphism b c)
>   -> functorOnMorphisms func a c (extCompose a b c g h)
>    = extCompose (f a) (f b) (f c) (functorOnMorphisms func a b g) (functorOnMorphisms func b c h)
> functorPreserveCompose func _ _ _ (MkExtensionalTypeMorphism g') (MkExtensionalTypeMorphism h')
>   = funExt (\x => functorComposition x g' h')
>
> functorToCFunctor :
>      VerifiedFunctor f
>   -> CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
>               TypesAsCategoryExtensional.typesAsCategoryExtensional
> functorToCFunctor {f} func = MkCFunctor
>   f
>   (functorOnMorphisms func)
>   (functorPreserveId func)
>   (functorPreserveCompose func)
