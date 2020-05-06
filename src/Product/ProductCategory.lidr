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

> module Product.ProductCategory
> 
> import Basic.Category
> import Basic.Functor
> import Data.Vect
> 
> %access public export
> %default total
> 
> productObject : (cats : Vect n Category) -> Type
> productObject [] = ()
> productObject (cat :: cats) = (obj cat, productObject cats)
> 
> productMorphism : (cats : Vect n Category) -> (a, b : productObject cats) -> Type
> productMorphism [] _ _ = ()
> productMorphism (cat :: cats) (a, as) (b, bs) = (mor cat a b, productMorphism cats as bs)
> 
> productIdentity : (cats : Vect n Category) -> (a : productObject cats) -> productMorphism cats a a
> productIdentity [] _ = ()
> productIdentity (cat :: cats) (a, as) = (identity cat a, productIdentity cats as)
> 
> productCompose : (cats : Vect n Category) -> (a, b, c : productObject cats) -> (f : productMorphism cats a b) -> (g : productMorphism cats b c) -> productMorphism cats a c
> productCompose [] _ _ _ _ _ = ()
> productCompose (cat :: cats) (a, as) (b, bs) (c, cs) (f, fs) (g, gs) = (compose cat a b c f g, productCompose cats as bs cs fs gs)
> 
> pairEq : (a = b, as = bs) -> (a, as) = (b, bs)
> pairEq (Refl, Refl) = Refl
> 
> productLeftIdentity : (cats : Vect n Category) -> (a, b : productObject cats) -> (f : productMorphism cats a b) -> productCompose cats a a b (productIdentity cats a) f = f
> productLeftIdentity [] _ _ () = Refl
> productLeftIdentity (cat :: cats) (a, as) (b, bs) (f, fs) = pairEq (leftIdentity cat a b f, productLeftIdentity cats as bs fs)
> 
> productRightIdentity : (cats : Vect n Category) -> (a, b : productObject cats) -> (f : productMorphism cats a b) -> productCompose cats a b b f (productIdentity cats b) = f
> productRightIdentity [] _ _ () = Refl
> productRightIdentity (cat :: cats) (a, as) (b, bs) (f, fs) = pairEq (rightIdentity cat a b f, productRightIdentity cats as bs fs)
> 
> productAssociativity : (cats : Vect n Category) -> (a, b, c, d : productObject cats) -> (f : productMorphism cats a b) -> (g : productMorphism cats b c) -> (h : productMorphism cats c d) -> productCompose cats a b d f (productCompose cats b c d g h) = productCompose cats a c d (productCompose cats a b c f g) h
> productAssociativity [] _ _ _ _ _ _ _ = Refl
> productAssociativity (cat :: cats) (a, as) (b, bs) (c, cs) (d, ds) (f, fs) (g, gs) (h, hs) = pairEq (associativity cat a b c d f g h, productAssociativity cats as bs cs ds fs gs hs)
> 
> productCategory : (cats : Vect n Category) -> Category
> productCategory cats = MkCategory
>   (productObject cats)
>   (productMorphism cats)
>   (productIdentity cats)
>   (productCompose cats)
>   (productLeftIdentity cats)
>   (productRightIdentity cats)
>   (productAssociativity cats)
