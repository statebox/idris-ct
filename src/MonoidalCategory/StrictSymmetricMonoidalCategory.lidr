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

> module MonoidalCategory.StrictSymmetricMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import MonoidalCategory.StrictMonoidalCategory
> import MonoidalCategory.SymmetricMonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> StrictUnitCoherence :
>      (cat : Category)
>   -> (unit : obj cat)
>   -> (symmetry : NaturalIsomorphism (productCategory cat cat)
>                                     cat
>                                     tensor
>                                     (functorComposition (productCategory cat cat)
>                                                         (productCategory cat cat)
>                                                         cat
>                                                         (swapFunctor cat cat)
>                                                         tensor))
>   -> (a : obj cat)
>   -> Type
> StrictUnitCoherence cat unit symmetry a =
>   (component (natTrans symmetry) (a, unit)) = identity cat a
>
> StrictAssociativityCoherence :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory cat cat) cat)
>   -> (tensorIsAssociativeObj :
>           (a, b, c : obj cat)
>        -> mapObj tensor (a, mapObj tensor (b, c)) = mapObj tensor (mapObj tensor (a, b), c))
>   -> (symmetry : NaturalIsomorphism (productCategory cat cat)
>                                     cat
>                                     tensor
>                                     (functorComposition (productCategory cat cat)
>                                                         (productCategory cat cat)
>                                                         cat
>                                                         (swapFunctor cat cat)
>                                                         tensor))
>   -> (a, b, c : obj cat)
>   -> Type
> StrictAssociativityCoherence cat tensor tensorIsAssociativeObj symmetry a b c =
>   component (natTrans symmetry) (a, mapObj tensor (b, c)) =
>   compose cat
>           (mapObj tensor (mapObj tensor (a, b), c))
>           (mapObj tensor (mapObj tensor (b, a), c))
>           (mapObj tensor (mapObj tensor (b, c), a))
>           (mapMor tensor
>                   (mapObj tensor (a, b), c)
>                   (mapObj tensor (b, a), c)
>                   (MkProductMorphism (component (natTrans symmetry) (a, b)) (identity cat c)))
>           (rewrite sym (tensorIsAssociativeObj b a c) in
>            rewrite sym (tensorIsAssociativeObj b c a) in (mapMor tensor
>                                                                  (b, (mapObj tensor (a, c)))
>                                                                  (b, (mapObj tensor (c, a)))
>                                                                  (MkProductMorphism (identity cat b)
>                                                                                     (component (natTrans symmetry)
>                                                                                                (a, c)))))
>
> data StrictSymmetricMonoidalCategory : Type where
>   MkStrictSymmetricMonoidalCategory :
>        (smcat : StrictMonoidalCategory)
>     -> (symmetry : NaturalIsomorphism (productCategory (cat smcat) (cat smcat))
>                                       (cat smcat)
>                                       (tensor smcat)
>                                       (functorComposition (productCategory (cat smcat) (cat smcat))
>                                                           (productCategory (cat smcat) (cat smcat))
>                                                           (cat smcat)
>                                                           (swapFunctor (cat smcat) (cat smcat))
>                                                           (tensor smcat)))
>     -> ((a : obj (cat smcat)) -> StrictUnitCoherence (cat smcat) (unit smcat) symmetry a)
>     -> ((a, b, c : obj (cat smcat)) -> StrictAssociativityCoherence (cat smcat)
>                                                                     (tensor smcat)
>                                                                     (tensorIsAssociativeObj smcat)
>                                                                     symmetry
>                                                                     a b c)
>     -> ((a, b : obj (cat smcat)) -> InverseLaw (cat smcat) (tensor smcat) symmetry a b)
>     -> StrictSymmetricMonoidalCategory
>
> smcat : StrictSymmetricMonoidalCategory -> StrictMonoidalCategory
> smcat (MkStrictSymmetricMonoidalCategory smcat _ _ _ _) = smcat
>
> symmetry :
>      (ssmc : StrictSymmetricMonoidalCategory)
>   -> NaturalIsomorphism (productCategory (cat (smcat ssmc)) (cat (smcat ssmc)))
>                         (cat (smcat ssmc))
>                         (tensor (smcat ssmc))
>                         (functorComposition (productCategory (cat (smcat ssmc)) (cat (smcat ssmc)))
>                                             (productCategory (cat (smcat ssmc)) (cat (smcat ssmc)))
>                                             (cat (smcat ssmc))
>                                             (swapFunctor (cat (smcat ssmc)) (cat (smcat ssmc)))
>                                             (tensor (smcat ssmc)))
> symmetry (MkStrictSymmetricMonoidalCategory _ symmetry _ _ _) = symmetry
