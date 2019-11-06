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

> module MonoidalCategory.MonoidalFunctor
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import MonoidalCategory.MonoidalCategory
> import Product.ProductCategory
> import Product.ProductFunctor
>
> %access public export
> %default total
>
> mapThenTensor :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> CFunctor (cat mcat1) (cat mcat2)
>   -> CFunctor (productCategory (cat mcat1) (cat mcat1)) (cat mcat2)
> mapThenTensor mcat1 mcat2 func = functorComposition
>   (productCategory (cat mcat1) (cat mcat1))
>   (productCategory (cat mcat2) (cat mcat2))
>   (cat mcat2)
>   (productFunctor func func)
>   (tensor mcat2)
>
> tensorThenMap :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> CFunctor (cat mcat1) (cat mcat2)
>   -> CFunctor (productCategory (cat mcat1) (cat mcat1)) (cat mcat2)
> tensorThenMap mcat1 mcat2 func = functorComposition
>   (productCategory (cat mcat1) (cat mcat1))
>   (cat mcat1)
>   (cat mcat2)
>   (tensor mcat1)
>   func
>
> PreserveMonoidalAssociativity :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> (func : CFunctor (cat mcat1) (cat mcat2))
>   -> NaturalTransformation (productCategory (cat mcat1) (cat mcat1))
>                            (cat mcat2)
>                            (mapThenTensor mcat1 mcat2 func)
>                            (tensorThenMap mcat1 mcat2 func)
>   -> mor (cat mcat2) (unit mcat2) (mapObj func (unit mcat1))
>   -> Type
> PreserveMonoidalAssociativity mcat1 mcat2 func coherenceNat coherenceMor =
>      (a, b, c : obj (cat mcat1))
>   -> compose (cat mcat2)
>              (mapObj (tensor mcat2) (mapObj (tensor mcat2) (mapObj func a, mapObj func b), mapObj func c))
>              (mapObj func (mapObj (tensor mcat1) (mapObj (tensor mcat1) (a, b), c)))
>              (mapObj func (mapObj (tensor mcat1) (a, mapObj (tensor mcat1) (b, c))))
>              (compose (cat mcat2)
>                       (mapObj (tensor mcat2) (mapObj (tensor mcat2) (mapObj func a, mapObj func b), mapObj func c))
>                       (mapObj (tensor mcat2) (mapObj func (mapObj (tensor mcat1) (a, b)), mapObj func c))
>                       (mapObj func (mapObj (tensor mcat1) (mapObj (tensor mcat1) (a, b), c)))
>                       (mapMor (tensor mcat2)
>                               (mapObj (tensor mcat2) (mapObj func a, mapObj func b), mapObj func c)
>                               (mapObj func (mapObj (tensor mcat1) (a, b)), mapObj func c)
>                               (MkProductMorphism (component coherenceNat (a, b))
>                                                  (identity (cat mcat2) (mapObj func c))))
>                       (component coherenceNat (mapObj (tensor mcat1) (a, b), c)))
>              (component (composeFunctorNatTrans (natTrans $ associator mcat1) func) (a, (b, c)))
>    = compose (cat mcat2)
>              (mapObj (tensor mcat2) (mapObj (tensor mcat2) (mapObj func a, mapObj func b), mapObj func c))
>              (mapObj (tensor mcat2) (mapObj func a, mapObj func (mapObj (tensor mcat1) (b, c))))
>              (mapObj func (mapObj (tensor mcat1) (a, mapObj (tensor mcat1) (b, c))))
>              (compose (cat mcat2)
>                       (mapObj (tensor mcat2) (mapObj (tensor mcat2) (mapObj func a, mapObj func b), mapObj func c))
>                       (mapObj (tensor mcat2) (mapObj func a, mapObj (tensor mcat2) (mapObj func b, mapObj func c)))
>                       (mapObj (tensor mcat2) (mapObj func a, mapObj func (mapObj (tensor mcat1) (b, c))))
>                       (component (natTrans (associator mcat2)) (mapObj func a, (mapObj func b, mapObj func c)))
>                       (mapMor (tensor mcat2)
>                               (mapObj func a, mapObj (tensor mcat2) (mapObj func b, mapObj func c))
>                               (mapObj func a, mapObj func (mapObj (tensor mcat1) (b, c)))
>                               (MkProductMorphism (identity (cat mcat2) (mapObj func a))
>                                                  (component coherenceNat (b, c)))))
>              (component coherenceNat (a, mapObj (tensor mcat1) (b, c)))
>
> PreserveMonoidalLeftId :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> (func : CFunctor (cat mcat1) (cat mcat2))
>   -> NaturalTransformation (productCategory (cat mcat1) (cat mcat1))
>                            (cat mcat2)
>                            (mapThenTensor mcat1 mcat2 func)
>                            (tensorThenMap mcat1 mcat2 func)
>   -> mor (cat mcat2) (unit mcat2) (mapObj func (unit mcat1))
>   -> Type
> PreserveMonoidalLeftId mcat1 mcat2 func coherenceNat coherenceMor =
>      (a : obj (cat mcat1))
>   -> component (natTrans (leftUnitor mcat2)) (mapObj func a)
>    = compose (cat mcat2) (mapObj (tensor mcat2) (unit mcat2, mapObj func a))
>                          (mapObj func (mapObj (tensor mcat1) (unit mcat1, a)))
>                          (mapObj func a)
>                          (compose (cat mcat2) (mapObj (tensor mcat2) (unit mcat2, mapObj func a))
>                                               (mapObj (tensor mcat2) (mapObj func (unit mcat1), mapObj func a))
>                                               (mapObj func (mapObj (tensor mcat1) (unit mcat1, a)))
>                                               (mapMor (tensor mcat2)
>                                                       (unit mcat2, mapObj func a)
>                                                       (mapObj func (unit mcat1), mapObj func a)
>                                                       (MkProductMorphism coherenceMor
>                                                                          (identity (cat mcat2) (mapObj func a))))
>                                               (component coherenceNat (unit mcat1, a)))
>                          (mapMor func
>                                  (mapObj (tensor mcat1) (unit mcat1, a))
>                                  a
>                                  (component (natTrans (leftUnitor mcat1)) a))
>
> PreserveMonoidalRightId :
>      (mcat1, mcat2 : MonoidalCategory)
>   -> (func : CFunctor (cat mcat1) (cat mcat2))
>   -> NaturalTransformation (productCategory (cat mcat1) (cat mcat1))
>                            (cat mcat2)
>                            (mapThenTensor mcat1 mcat2 func)
>                            (tensorThenMap mcat1 mcat2 func)
>   -> mor (cat mcat2) (unit mcat2) (mapObj func (unit mcat1))
>   -> Type
> PreserveMonoidalRightId mcat1 mcat2 func coherenceNat coherenceMor =
>      (a : obj (cat mcat1))
>   -> component (natTrans (rightUnitor mcat2)) (mapObj func a)
>    = compose (cat mcat2) (mapObj (tensor mcat2) (mapObj func a, unit mcat2))
>                          (mapObj func (mapObj (tensor mcat1) (a, unit mcat1)))
>                          (mapObj func a)
>                          (compose (cat mcat2) (mapObj (tensor mcat2) (mapObj func a, unit mcat2))
>                                               (mapObj (tensor mcat2) (mapObj func a, mapObj func (unit mcat1)))
>                                               (mapObj func (mapObj (tensor mcat1) (a, unit mcat1)))
>                                               (mapMor (tensor mcat2)
>                                                       (mapObj func a, unit mcat2)
>                                                       (mapObj func a, mapObj func (unit mcat1))
>                                                       (MkProductMorphism (identity (cat mcat2) (mapObj func a))
>                                                                          coherenceMor))
>                                               (component coherenceNat (a, unit mcat1)))
>                          (mapMor func
>                                  (mapObj (tensor mcat1) (a, unit mcat1))
>                                  a
>                                  (component (natTrans (rightUnitor mcat1)) a))
>
> -- we are not using a record here because compilation does not terminate in that case
> data MonoidalFunctor : (mcat1, mcat2 : MonoidalCategory) -> Type where
>   MkMonoidalFunctor :
>        (func :  CFunctor (cat mcat1) (cat mcat2))
>     -> (coherenceNat : NaturalTransformation (productCategory (cat mcat1) (cat mcat1))
>                                              (cat mcat2)
>                                              (mapThenTensor mcat1 mcat2 func)
>                                              (tensorThenMap mcat1 mcat2 func))
>     -> (coherenceMor : mor (cat mcat2) (unit mcat2) (mapObj func (unit mcat1)))
>     -> (preserveAssociativity : PreserveMonoidalAssociativity mcat1 mcat2 func coherenceNat coherenceMor)
>     -> (preserveLeftId : PreserveMonoidalLeftId mcat1 mcat2 func coherenceNat coherenceMor)
>     -> (preserveRightId : PreserveMonoidalRightId mcat1 mcat2 func coherenceNat coherenceMor)
>     -> MonoidalFunctor mcat1 mcat2
