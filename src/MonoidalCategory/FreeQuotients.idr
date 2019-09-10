-- \iffalse
-- SPDX-License-Identifier: AGPL-3.0-only

-- This file is part of `idris-ct` Category Theory in Idris library.

-- Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.

-- You should have received a copy of the GNU Affero General Public License
-- along with this program.  If not, see <https://www.gnu.org/licenses/>.
-- \fi

module MonoidalCategory.FreeMonoidalCategory

import Basic.Category
import Basic.Functor
import Basic.Isomorphism
import Basic.NaturalIsomorphism
import Basic.NaturalTransformation
import Data.List
import Monoid.FreeMonoid
import Monoid.Monoid
import MonoidalCategory.StrictMonoidalCategory
import MonoidalCategory.StrictSymmetricMonoidalCategory
import MonoidalCategory.SymmetricMonoidalCategoryHelpers
import Product.ProductCategory
import Quotient.Quotient
import Quotient.UnsafeQuotient

%access public export
%default total

parameters (t : Type, generatingMorphisms : List (List t, List t), extra : (List t -> List t -> Type) -> List t -> List t -> Type)

  data PreFreeMorphism : List t -> List t -> Type where
    MkIdFreeMorphism          : (x : List t) -> PreFreeMorphism x x
    MkCompositionFreeMorphism : PreFreeMorphism a b
                             -> PreFreeMorphism b c
                             -> PreFreeMorphism a c
    MkGeneratingFreeMorphism  : (e : (List t, List t))
                             -> Elem e generatingMorphisms
                             -> PreFreeMorphism (Basics.fst e) (Basics.snd e)
    MkExtra                   : extra PreFreeMorphism a b -> PreFreeMorphism a b

  data PreFreeMorphismEquality : (domain, codomain : List t) -> Rel (PreFreeMorphism domain codomain) where
    LeftIdentityEq : (as, bs : List t)
                  -> (fm : PreFreeMorphism as bs)
                  -> PreFreeMorphismEquality as bs (MkCompositionFreeMorphism (MkIdFreeMorphism as) fm) fm
    RightIdentityEq : (as, bs : List t)
                  -> (fm : PreFreeMorphism as bs)
                  -> PreFreeMorphismEquality as bs (MkCompositionFreeMorphism fm (MkIdFreeMorphism bs)) fm
    AssociativeEq : (as, bs, cs, ds : List t)
                 -> (fm1 : PreFreeMorphism as bs)
                 -> (fm2 : PreFreeMorphism bs cs)
                 -> (fm3 : PreFreeMorphism cs ds)
                 -> PreFreeMorphismEquality as ds
                                         (MkCompositionFreeMorphism fm1 (MkCompositionFreeMorphism fm2 fm3))
                                         (MkCompositionFreeMorphism (MkCompositionFreeMorphism fm1 fm2) fm3)

  FreeMorphism : (a, b : List t) -> Quotient' (PreFreeMorphism a b) (PreFreeMorphismEquality a b)
  FreeMorphism a b = UnsafeQuotient' (PreFreeMorphism a b) (PreFreeMorphismEquality a b)

parameters (t : Type, generatingMorphisms : List (List t, List t))

  data PreFreeMonoidalMorphism : ((List t -> List t -> Type) -> List t -> List t -> Type) -> List t -> List t -> Type where
    MkMonoidalFromFree          : PreFreeMorphism t generatingMorphisms extra a b -> PreFreeMonoidalMorphism extra a b
    MkJuxtapositionFreeMorphism : PreFreeMonoidalMorphism extra a b
                               -> PreFreeMonoidalMorphism extra c d
                               -> PreFreeMonoidalMorphism extra (a ++ c) (b ++ d)
    MkExtraMonoidal             : extra (PreFreeMonoidalMorphism extra) a b -> PreFreeMonoidalMorphism extra a b

  IdFreeMonoidalMorphism : (x : List t) -> PreFreeMonoidalMorphism extra x x
  IdFreeMonoidalMorphism x = MkMonoidalFromFree $ MkIdFreeMorphism _ _ _ x

  data PreFreeMonoidalMorphismEquality : (extra : (List t -> List t -> Type) -> List t -> List t -> Type)
                                      -> (domain, codomain : List t)
                                      -> Rel (PreFreeMonoidalMorphism extra domain codomain) where
    FreeTensorIdEq : (a, b : List t)
                  -> PreFreeMonoidalMorphismEquality extra (a ++ b) (a ++ b)
                       (MkJuxtapositionFreeMorphism (IdFreeMonoidalMorphism a) (IdFreeMonoidalMorphism b))
                       (IdFreeMonoidalMorphism (a ++ b))

-- parameters (t : Type, generatingMorphisms : List (List t, List t), extra : List t -> List t -> Type)

--   data PreFreeSymmetricMonoidalMorphismExtra : List t -> List t -> Type where
--     MkSymmetryFreeMorphism : (x, y : List t) -> PreFreeSymmetricMonoidalMorphismExtra (x ++ y) (y ++ x)
--     MkExtraSymmetric       : extra a b -> PreFreeSymmetricMonoidalMorphismExtra a b

--   PreFreeSymmetricMonoidalMorphism : List t -> List t -> Type
--   PreFreeSymmetricMonoidalMorphism = PreFreeMonoidalMorphism t generatingMorphisms PreFreeSymmetricMonoidalMorphismExtra
