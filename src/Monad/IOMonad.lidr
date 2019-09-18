attach\iffalse
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

> module Monad.IOMonad
>
> import Basic.Category
> import Idris.TypesAsCategoryExtensional
> import Monad.Monad as M
> import Monad.VerifiedMonadAsMonad
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> postulate
> ioId :
>      (io : IO' ffi a)
>   -> io >>= pure = io
>
> postulate
> ioCompose :
>      (io : IO' ffi a)
>   -> (f : a -> b)
>   -> (g : b -> c)
>   -> map (g . f) io = (map g . map f) io
>
> VerifiedFunctor (IO' ffi) where
>   functorIdentity = \_, _ => ioId
>   functorComposition = ioCompose
>
> postulate
> ioMLeftIdentity :
>      (x : a)
>   -> (f : a -> IO' ffi b)
>   -> pure x >>= f = f x
>
> ioAMap :
>      (io : IO' ffi a)
>   -> (f : a -> b)
>   -> map f io = pure f <*> io
> ioAMap io f = rewrite ioMLeftIdentity f (\g => io >>= (pure . g)) in Refl
>
> postulate
> ioAIdentity :
>      (io : IO' ffi a)
>   -> pure Basics.id <*> io = io
>
> postulate
> ioAComposition :
>      (io : IO' ffi  a)
>   -> (f  : IO' ffi (a -> b))
>   -> (g  : IO' ffi (b -> c))
>   -> ((pure (.) <*> g) <*> f) <*> io = g <*> (f <*> io)
>
> postulate
> ioAHomomorphism :
>      (x : a)
>   -> (f : a -> b)
>   -> (<*>) {f = IO' ffi} (pure f) (pure x) = pure (f x)
>
> postulate
> ioAInterchange :
>      (x : a)
>   -> (f : IO' ffi (a -> b))
>   -> f <*> pure x = pure (\g : (a -> b) => g x) <*> f
>
> VerifiedApplicative (IO' ffi) where
>   applicativeMap = ioAMap
>   applicativeIdentity = ioAIdentity
>   applicativeComposition = ioAComposition
>   applicativeHomomorphism = ioAHomomorphism
>   applicativeInterchange = ioAInterchange
>
> ioMApplicative :
>      (mf : IO' ffi (a -> b))
>   -> (io : IO' ffi a)
>   -> mf <*> io = mf >>= \f =>
>                  io >>= \x =>
>                         pure (f x)
> ioMApplicative mf io = Refl
>
> postulate
> ioMRightIdentity :
>      (io : IO' ffi a)
>   -> io >>= pure = io
>
> postulate
> ioMAssociativity :
>      (io : IO' ffi a)
>   -> (f : a -> IO' ffi b)
>   -> (g : b -> IO' ffi c)
>   -> (io >>= f) >>= g = io >>= (\x => f x >>= g)
>
> VerifiedMonad (IO' ffi) where
>   monadApplicative = ioMApplicative
>   monadLeftIdentity = ioMLeftIdentity
>   monadRightIdentity = ioMRightIdentity
>   monadAssociativity = ioMAssociativity
>
> ioMonad : FFI -> M.Monad TypesAsCategoryExtensional.typesAsCategoryExtensional
> ioMonad ffi = verifiedMonadToExtMonad {m = IO' ffi}
