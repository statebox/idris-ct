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

> module Monad.VerifiedMonadAsMonad
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Idris.FunctorAsCFunctor
> import Idris.TypesAsCategoryExtensional
> import Monad.Monad as M
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> verifiedMonadToFunctor : VerifiedMonad m => Functor m
> verifiedMonadToFunctor = %implementation
>
> verifiedMonadToVerifiedFunctor : VerifiedMonad m => VerifiedFunctor m
> verifiedMonadToVerifiedFunctor = %implementation
>
> verifiedMonadToApplicative : VerifiedMonad m => Applicative m
> verifiedMonadToApplicative = %implementation
>
> verifiedMonadToVerifiedApplicative : VerifiedMonad m => VerifiedApplicative m
> verifiedMonadToVerifiedApplicative = %implementation
>
> verifiedMonadToMonad : VerifiedMonad m => Monad m
> verifiedMonadToMonad = %implementation
>
> verifiedMonadToCFunctor : VerifiedMonad m => CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                       TypesAsCategoryExtensional.typesAsCategoryExtensional
> verifiedMonadToCFunctor {m} = functorToCFunctor $ verifiedMonadToVerifiedFunctor {m}
>
> verifiedMonadMapPure : VerifiedMonad m =>
>      (g : a -> b)
>   -> (x : a)
>   -> map {f = m} g (pure x) = pure (g x)
> verifiedMonadMapPure {m} g x = trans (applicativeMap @{verifiedMonadToVerifiedApplicative {m}} (pure x) g)
>                                      (applicativeHomomorphism @{verifiedMonadToVerifiedApplicative {m}} x g)
>
> verifiedMonadUnit : VerifiedMonad m =>
>   NaturalTransformation _ _ (idFunctor _) (verifiedMonadToCFunctor {m})
> verifiedMonadUnit {m} = MkNaturalTransformation
>   (\_ => MkExtensionalTypeMorphism $ pure)
>   (\a, b, (MkExtensionalTypeMorphism g) => funExt $ verifiedMonadMapPure {m} g)
>
> verifiedMonadMultiplicationComp : VerifiedMonad m =>
>   mor TypesAsCategoryExtensional.typesAsCategoryExtensional
>       (mapObj (verifiedMonadToCFunctor {m}) (mapObj (verifiedMonadToCFunctor {m}) a))
>       (mapObj (verifiedMonadToCFunctor {m}) a)
> verifiedMonadMultiplicationComp = MkExtensionalTypeMorphism $ \x => x >>= Basics.id
>
> verifiedMonadMapAsBind : VerifiedMonad m =>
>      (x : m a)
>   -> (g : a -> b)
>   -> map g x = x >>= \y => pure (g y)
> verifiedMonadMapAsBind x g = trans
>   (applicativeMap x g)
>   (trans (monadApplicative (pure g) x)
>          (monadLeftIdentity g (\f => x >>= (\y => pure (f y)))))
>
> -- proving these lemmas would require function extensionality and we don't want its whole power for now
> -- hence we postulate only the special cases we need
> postulate
> verifiedMonadMapAsBindExt : VerifiedMonad m =>
>      (g : a -> b)
>   -> (\y => pure {f = m} (map {f = m} g y)) = (\y => pure (y >>= \z => pure (g z)))
>
> postulate
> verifiedMonadLeftIdentityExt : VerifiedMonad m =>
>      (g : a -> b)
>   -> (\y => (pure {f = m} ((>>=) {m} y (\z => pure {f = m} (g z)))) >>= Basics.id)
>    = (\y => (>>=) {m} y (\z => pure {f = m} (g z)))
>
> verifiedMonadMapJoin : VerifiedMonad m =>
>      (g : a -> b)
>   -> (x : m (m a))
>   -> map g (x >>= Basics.id) = map (map g) x >>= Basics.id
> verifiedMonadMapJoin {m} g x =
>   rewrite verifiedMonadMapAsBind {m} (x >>= Basics.id) g in
>   rewrite verifiedMonadMapAsBind {m} x (map g) in
>   rewrite monadAssociativity x Basics.id (\y => pure (g y)) in
>   rewrite verifiedMonadMapAsBindExt {m} g in
>   rewrite monadAssociativity x (\y => pure (y >>= (\z => pure (g z)))) Basics.id in
>   rewrite verifiedMonadLeftIdentityExt {m} g in Refl
>
> verifiedMonadMultiplication : VerifiedMonad m =>
>   NaturalTransformation _ _ (functorComposition _ _ _ (verifiedMonadToCFunctor {m})
>                                                       (verifiedMonadToCFunctor {m}))
>                             (verifiedMonadToCFunctor {m})
> verifiedMonadMultiplication {m} = MkNaturalTransformation
>   (\_ => verifiedMonadMultiplicationComp {m})
>   (\a, b, (MkExtensionalTypeMorphism g) => funExt $ verifiedMonadMapJoin {m} g)
>
> postulate
> verifiedMonadLeftIdentityExt' : VerifiedMonad m =>
>   (\y => pure ((>>=) {m} y Basics.id) >>= Basics.id) = (\y => y >>= Basics.id)
>
> verifiedMonadAssociativityComp : VerifiedMonad m =>
>      (x : m (m (m a)))
>   -> map (\y => y >>= Basics.id) x >>= Basics.id = x >>= Basics.id >>= Basics.id
> verifiedMonadAssociativityComp {m} x =
>   rewrite verifiedMonadMapAsBind {m} x (\y => y >>= Basics.id) in
>   rewrite monadAssociativity x (\y => pure (y >>= Basics.id)) Basics.id in
>   -- rewrite functorIdentity (map Basics.id) (\v => functorIdentity Basics.id (\w => Refl) v) x in
>   rewrite monadAssociativity x Basics.id Basics.id in
>   cong {f = (>>=) x} (verifiedMonadLeftIdentityExt' {m})
>
> verifiedMonadAssociativity : VerifiedMonad m =>
>   MonadAssociativity (verifiedMonadToCFunctor {m}) (verifiedMonadMultiplication {m})
> verifiedMonadAssociativity {m} = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ \x => verifiedMonadAssociativityComp {m} {a} x)
>
> verifiedMonadLeftUnit : VerifiedMonad m =>
>   MonadLeftUnit (verifiedMonadToCFunctor {m}) (verifiedMonadUnit {m}) (verifiedMonadMultiplication {m})
> verifiedMonadLeftUnit = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ \x => monadLeftIdentity x Basics.id)
>
> postulate
> verifiedMonadPurePureExt : VerifiedMonad m =>
>   (\y => pure (pure {f = m} y) >>= Basics.id) = pure
>
> verifiedMonadRightUnitComp : VerifiedMonad m =>
>      (x : m a)
>   -> map Applicative.pure x >>= Basics.id = x
> verifiedMonadRightUnitComp {m} x =
>   trans (cong {f = \y => y >>= Basics.id} (verifiedMonadMapAsBind {m} x Applicative.pure))
>   (trans (monadAssociativity x (\y => pure (pure y)) Basics.id)
>   (trans (cong {f = (>>=) x} (verifiedMonadPurePureExt {m})) (monadRightIdentity x)))
>
> verifiedMonadRightUnit : VerifiedMonad m =>
>    MonadRightUnit (verifiedMonadToCFunctor {m}) (verifiedMonadUnit {m}) (verifiedMonadMultiplication {m})
> verifiedMonadRightUnit {m} = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ verifiedMonadRightUnitComp {m})
>
> verifiedMonadToExtMonad : VerifiedMonad m =>
>   M.Monad TypesAsCategoryExtensional.typesAsCategoryExtensional
> verifiedMonadToExtMonad {m} = MkMonad
>   (verifiedMonadToCFunctor {m})
>   (verifiedMonadUnit {m})
>   (verifiedMonadMultiplication {m})
>   (verifiedMonadAssociativity {m})
>   (verifiedMonadLeftUnit {m})
>   (verifiedMonadRightUnit {m})
