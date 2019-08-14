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
> import Syntax.PreorderReasoning
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> verifiedMonadToFunctor : VerifiedMonad m => Functor m
> verifiedMonadToFunctor @{monad} = %implementation
>
> verifiedMonadToVerifiedFunctor : VerifiedMonad m => VerifiedFunctor m
> verifiedMonadToVerifiedFunctor @{monad} = %implementation
>
> verifiedMonadToApplicative : VerifiedMonad m => Applicative m
> verifiedMonadToApplicative @{monad} = %implementation
>
> verifiedMonadToVerifiedApplicative : VerifiedMonad m => VerifiedApplicative m
> verifiedMonadToVerifiedApplicative @{monad} = %implementation
>
> verifiedMonadToMonad : VerifiedMonad m => Monad m
> verifiedMonadToMonad @{monad} = %implementation
>
> verifiedMonadToCFunctor : VerifiedMonad m => CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                       TypesAsCategoryExtensional.typesAsCategoryExtensional
> verifiedMonadToCFunctor @{monad} = functorToCFunctor $ verifiedMonadToVerifiedFunctor @{monad}
>
> verifiedMonadMapPure :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (x : a)
>   -> map {f = m} g (pure x) = pure (g x)
> verifiedMonadMapPure monad g x = trans (applicativeMap @{verifiedMonadToVerifiedApplicative @{monad}} (pure x) g)
>                                        (applicativeHomomorphism @{verifiedMonadToVerifiedApplicative @{monad}} x g)
>
> verifiedMonadUnit :
>      (monad : VerifiedMonad m)
>   -> NaturalTransformation _ _ (idFunctor _) (verifiedMonadToCFunctor @{monad})
> verifiedMonadUnit {m} monad = MkNaturalTransformation
>   (\_ => MkExtensionalTypeMorphism $ pure)
>   (\a, b, f => case f of
>                  MkExtensionalTypeMorphism g => funExt $ verifiedMonadMapPure monad g)
>
> verifiedMonadMultiplicationComp :
>      (monad : VerifiedMonad m)
>   -> (a : Type)
>   -> mor TypesAsCategoryExtensional.typesAsCategoryExtensional
>          (mapObj (verifiedMonadToCFunctor @{monad}) (mapObj (verifiedMonadToCFunctor @{monad}) a))
>          (mapObj (verifiedMonadToCFunctor @{monad}) a)
> verifiedMonadMultiplicationComp monad a = MkExtensionalTypeMorphism $ \x => x >>= Basics.id
>
> verifiedMonadMapAsBind :
>      (monad : VerifiedMonad m)
>   -> (x : m a)
>   -> (g : a -> b)
>   -> map g x = x >>= \y => pure (g y)
> verifiedMonadMapAsBind monad x g = trans
>   (applicativeMap x g)
>   (trans (monadApplicative (pure g) x)
>          (monadLeftIdentity g (\f => x >>= (\y => pure (f y)))))
>
> -- proving these lemmas would require function extensionality and we don't want its whole power for now
> -- hence we postulate only the special cases we need
> postulate
> verifiedMonadMapAsBindExt :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (\y => pure {f = m} (map {f = m} g y)) = (\y => pure (y >>= \z => pure (g z)))
>
> postulate
> verifiedMonadLeftIdentityExt :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (\y => (pure {f = m} ((>>=) {m} y (\z => pure {f = m} (g z)))) >>= Basics.id)
>    = (\y => (>>=) {m} y (\z => pure {f = m} (g z)))
>
> verifiedMonadMapJoin :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (x : m (m a))
>   -> map g (x >>= Basics.id) = map (map g) x >>= Basics.id
> verifiedMonadMapJoin monad g x =
>   rewrite verifiedMonadMapAsBind monad (x >>= Basics.id) g in
>   rewrite verifiedMonadMapAsBind monad x (map g) in
>   rewrite monadAssociativity x Basics.id (\y => pure (g y)) in
>   rewrite verifiedMonadMapAsBindExt monad g in
>   rewrite monadAssociativity x (\y => pure (y >>= (\z => pure (g z)))) Basics.id in
>   rewrite verifiedMonadLeftIdentityExt monad g in Refl
>
> verifiedMonadMultiplication :
>      (monad : VerifiedMonad m)
>   -> NaturalTransformation _ _ (functorComposition _ _ _ (verifiedMonadToCFunctor @{monad})
>                                                          (verifiedMonadToCFunctor @{monad}))
>                                (verifiedMonadToCFunctor @{monad})
> verifiedMonadMultiplication monad = MkNaturalTransformation
>   (verifiedMonadMultiplicationComp monad)
>   (\a, b, f => case f of
>                  MkExtensionalTypeMorphism g => funExt $ verifiedMonadMapJoin monad g)
>
> postulate
> verifiedMonadLeftIdentityExt' :
>      (monad : VerifiedMonad m)
>   -> (\y => pure ((>>=) {m} y Basics.id) >>= Basics.id) = (\y => y >>= Basics.id)
>
> verifiedMonadAssociativityComp :
>      (monad : VerifiedMonad m)
>   -> (x : m (m (m a)))
>   -> map (\y => y >>= Basics.id) x >>= Basics.id = x >>= Basics.id >>= Basics.id
> verifiedMonadAssociativityComp monad x =
>   rewrite verifiedMonadMapAsBind monad x (\y => y >>= Basics.id) in
>   rewrite monadAssociativity x (\y => pure (y >>= Basics.id)) Basics.id in
>   rewrite monadAssociativity x Basics.id Basics.id in
>   cong {f = (>>=) x} (verifiedMonadLeftIdentityExt' monad)
>
> verifiedMonadAssociativity :
>      (monad : VerifiedMonad m)
>   -> MonadAssociativity (verifiedMonadToCFunctor @{monad}) (verifiedMonadMultiplication monad)
> verifiedMonadAssociativity monad = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ \x => verifiedMonadAssociativityComp monad {a} x)
>
> verifiedMonadLeftUnit :
>      (monad : VerifiedMonad m)
>   -> MonadLeftUnit (verifiedMonadToCFunctor @{monad}) (verifiedMonadUnit monad) (verifiedMonadMultiplication monad)
> verifiedMonadLeftUnit monad = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ \x => monadLeftIdentity x Basics.id)
>
> postulate
> verifiedMonadPurePureExt :
>      (monad : VerifiedMonad m)
>   -> (\y => pure (pure {f = m} y) >>= Basics.id) = pure
>
> verifiedMonadRightUnitComp :
>      (monad : VerifiedMonad m)
>   -> (x : m a)
>   -> map Applicative.pure x >>= Basics.id = x
> verifiedMonadRightUnitComp monad x =
>   trans (cong {f = \y => y >>= Basics.id} (verifiedMonadMapAsBind monad x Applicative.pure))
>   (trans (monadAssociativity x (\y => pure (pure y)) Basics.id)
>   (trans (cong {f = (>>=) x} (verifiedMonadPurePureExt monad)) (monadRightIdentity x)))
>
> verifiedMonadRightUnit :
>      (monad : VerifiedMonad m)
>   -> MonadRightUnit (verifiedMonadToCFunctor @{monad}) (verifiedMonadUnit monad) (verifiedMonadMultiplication monad)
> verifiedMonadRightUnit monad = naturalTransformationExt _ _ _ _ _ _
>   (\a => funExt $ verifiedMonadRightUnitComp monad)
>
> verifiedMonadToExtMonad :
>      VerifiedMonad m
>   -> M.Monad TypesAsCategoryExtensional.typesAsCategoryExtensional
> verifiedMonadToExtMonad {m} monad = MkMonad
>   (functorToCFunctor $ verifiedMonadToVerifiedFunctor @{monad})
>   (verifiedMonadUnit @{monad})
>   (verifiedMonadMultiplication @{monad})
>   (verifiedMonadAssociativity @{monad})
>   (verifiedMonadLeftUnit @{monad})
>   (verifiedMonadRightUnit @{monad})
