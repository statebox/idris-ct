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

> module Product.ProductFunctor
> 
> import Basic.Category
> import Basic.Functor
> import Product.ProductCategory
> import Data.Vect
> 
> %access public export
> %default total
> 
> fsts : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)) -> Vect n Category
> fsts [] = []
> fsts (((c, d) ** f) :: fs) = c :: fsts fs
> 
> snds : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)) -> Vect n Category
> snds [] = []
> snds (((c, d) ** f) :: fs) = d :: snds fs
> 
> mObj :
>      (functors : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)))
>   -> obj (ProductCategory.productCategory (fsts functors))
>   -> obj (ProductCategory.productCategory (snds functors))
> mObj [] _ = ()
> mObj (((_, _) ** f) :: fs) (a, as) = (mapObj f a, mObj fs as)
> 
> mMor :
>      (functors : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)))
>   -> (a, b : obj (productCategory (fsts functors)))
>   -> mor (productCategory (fsts functors)) a b
>   -> mor (productCategory (snds functors)) (mObj functors a) (mObj functors b)
> mMor [] _ _ _ = ()
> mMor (((_, _) ** f) :: fs) (a, as) (b, bs) (m, ms) = (mapMor f a b m, mMor fs as bs ms)
> 
> preserveId :
>      (functors : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)))
>   -> (a : obj (productCategory (fsts functors)))
>   -> mMor functors a a (identity (productCategory (fsts functors)) a) = identity (productCategory (snds functors)) (mObj functors a)
> preserveId [] _ = Refl
> preserveId (((_, _) ** f) :: fs) (a, as) = pairEq (preserveId f a, preserveId fs as)
> 
> preserveCompose :
>      (functors : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)))
>   -> (a, b, c : obj (productCategory (fsts functors)))
>   -> (f : mor (productCategory (fsts functors)) a b)
>   -> (g : mor (productCategory (fsts functors)) b c)
>   -> mMor functors a c (compose (productCategory (fsts functors)) a b c f g)
>    = compose (productCategory (snds functors)) (mObj functors a) (mObj functors b) (mObj functors c) (mMor functors a b f) (mMor functors b c g)
> preserveCompose [] _ _ _ _ _ = Refl
> preserveCompose (((_, _) ** func) :: funcs) (a, as) (b, bs) (c, cs) (f, fs) (g, gs) = pairEq (preserveCompose func a b c f g, preserveCompose funcs as bs cs fs gs)
> 
> productFunctor :
>      (functors : Vect n (cats : (Category, Category) ** CFunctor (Basics.fst cats) (Basics.snd cats)))
>   -> CFunctor (productCategory (fsts functors)) (productCategory (snds functors))
> productFunctor functors = MkCFunctor
>   (mObj functors)
>   (mMor functors)
>   (preserveId functors)
>   (preserveCompose functors)
