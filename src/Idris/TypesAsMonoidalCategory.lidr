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

> module Idris.TypesAsMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Idris.TypesAsCategoryExtensional
> import MonoidalCategory.MonoidalCategory
> import MonoidalCategory.MonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access public export
> %default total
>
> typesTensorMorphism :
>      (a, b : (Type, Type))
>   -> ProductMorphism TypesAsCategoryExtensional.typesAsCategoryExtensional
>                      TypesAsCategoryExtensional.typesAsCategoryExtensional
>                      a b
>   -> ExtensionalTypeMorphism (fst a, snd a) (fst b, snd b)
> typesTensorMorphism a b f = MkExtensionalTypeMorphism $ \(t1, t2) => (func (pi1 f) $ t1, func (pi2 f) $ t2)
>
> typesTensorPreservesId :
>      (a : (Type, Type))
>   -> typesTensorMorphism a a (MkProductMorphism (MkExtensionalTypeMorphism (id {a = fst a}))
>                                                 (MkExtensionalTypeMorphism (id {a = snd a})))
>    = MkExtensionalTypeMorphism id
> typesTensorPreservesId a = funExt (\(t1, t2) => Refl)
>
> typesTensor : CFunctor (productCategory TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                         TypesAsCategoryExtensional.typesAsCategoryExtensional)
>                        TypesAsCategoryExtensional.typesAsCategoryExtensional
> typesTensor = MkCFunctor
>   (\ab => (fst ab, snd ab))
>   (\a, b, f => typesTensorMorphism a b f)
>   (\a => typesTensorPreservesId a)
>   (\a, b, c, f, g => ?pComp)
>
> typesAssociator : Associator TypesAsCategoryExtensional.typesAsCategoryExtensional TypesAsMonoidalCategory.typesTensor
>
> typesLeftUnitor : NaturalIsomorphism TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                      TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                      (leftIdTensor TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                    TypesAsMonoidalCategory.typesTensor
>                                                    ())
>                                      (idFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional)
>
> typesRightUnitor : NaturalIsomorphism TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                       TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                       (rightIdTensor TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                      TypesAsMonoidalCategory.typesTensor
>                                                      ())
>                                       (idFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional)
>
> typesPentagon : (a, b, c, d : Type) -> MonoidalPentagon TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                         TypesAsMonoidalCategory.typesTensor
>                                                         TypesAsMonoidalCategory.typesAssociator
>                                                         a b c d
>
> typesTriangle : (a, b : Type) -> MonoidalTriangle TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                   TypesAsMonoidalCategory.typesTensor
>                                                   ()
>                                                   TypesAsMonoidalCategory.typesAssociator
>                                                   TypesAsMonoidalCategory.typesLeftUnitor
>                                                   TypesAsMonoidalCategory.typesRightUnitor
>                                                   a b
>
> typesAsMonoidalCategory : MonoidalCategory
> typesAsMonoidalCategory = MkMonoidalCategory
>   TypesAsCategoryExtensional.typesAsCategoryExtensional
>   typesTensor
>   ()
>   typesAssociator
>   typesLeftUnitor
>   typesRightUnitor
>   typesPentagon
>   typesTriangle
