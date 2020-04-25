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

> module CoLimits.CoProduct
>
> import Basic.Category
> import Basic.Isomorphism
>
> %access public export
> %default total
> %auto_implicits off
>
> record CommutingMorphism
>  (cat : Category)
>  (l : obj cat) (r : obj cat) (carrier : obj cat) (c : obj cat)
>  (inl : mor cat l carrier) (inr : mor cat r carrier)
>  (f : mor cat l c) (g : mor cat r c)
> where
>   constructor MkCommutingMorphism
>   challenger         : mor cat carrier c
>   commutativityLeft  : compose cat l carrier c inl challenger = f
>   commutativityRight : compose cat r carrier c inr challenger = g
>
> record CoProduct
>   (cat : Category)
>   (l : obj cat) (r : obj cat)
> where
>   constructor MkCoProduct
>   carrier: obj cat
>   inl: mor cat l carrier
>   inr: mor cat r carrier
>   exists:
>        (c : obj cat)
>     -> (f : mor cat l c)
>     -> (g : mor cat r c)
>     -> CommutingMorphism cat l r carrier c inl inr f g
>   unique:
>        (c : obj cat)
>     -> (f : mor cat l c)
>     -> (g : mor cat r c)
>     -> (h : CommutingMorphism cat l r carrier c inl inr f g)
>     -> challenger h = challenger (exists c f g)
>
> coProductMorphism :
>      (cat : Category)
>   -> (l, r : obj cat)
>   -> (a, b : CoProduct cat l r)
>   -> CommutingMorphism
>        cat
>        l r (carrier a) (carrier b)
>        (inl a) (inr a)
>        (inl b) (inr b)
> coProductMorphism cat l r a b = exists a (carrier b) (inl b) (inr b)
>
> composeCoProductMorphisms :
>      (cat : Category)
>   -> (l, r : obj cat)
>   -> (a, b : CoProduct cat l r)
>   -> CommutingMorphism
>        cat
>        l r (carrier a) (carrier a)
>        (inl a) (inr a)
>        (inl a) (inr a)
> composeCoProductMorphisms cat l r a b =
>   let
>     mor = coProductMorphism cat l r a b
>     inv = coProductMorphism cat l r b a
>   in
>     MkCommutingMorphism
>       (compose cat (carrier a) (carrier b) (carrier a)
>         (challenger mor) (challenger inv))
>       (rewrite associativity cat l (carrier a) (carrier b) (carrier a)
>                (inl a) (challenger mor) (challenger inv) in
>        rewrite commutativityLeft mor in
>        rewrite commutativityLeft inv in Refl)
>       (rewrite associativity cat r (carrier a) (carrier b) (carrier a)
>                (inr a) (challenger mor) (challenger inv) in
>        rewrite commutativityRight mor in
>        rewrite commutativityRight inv in Refl)
>
> idCommutingMorphism :
>      (cat : Category)
>   -> (l, r : obj cat)
>   -> (a : CoProduct cat l r)
>   -> CommutingMorphism
>        cat
>        l r (carrier a) (carrier a)
>        (inl a) (inr a)
>        (inl a) (inr a)
> idCommutingMorphism cat l r a = MkCommutingMorphism
>   (identity cat (carrier a))
>   (rightIdentity cat l (carrier a) (inl a))
>   (rightIdentity cat r (carrier a) (inr a))
>
> coProductsAreIsomorphic :
>      (cat : Category)
>   -> (l, r : obj cat)
>   -> (a, b : CoProduct cat l r)
>   -> Isomorphic cat (carrier a) (carrier b)
> coProductsAreIsomorphic cat l r a b =
>   let
>     mor = coProductMorphism cat l r a b
>     inv = coProductMorphism cat l r b a
>   in
>     buildIsomorphic
>       (challenger mor)
>       (challenger inv)
>       (rewrite unique a (carrier a) (inl a) (inr a)
>                         (composeCoProductMorphisms cat l r a b) in
>        rewrite unique a (carrier a) (inl a) (inr a)
>                         (idCommutingMorphism cat l r a) in Refl)
>       (rewrite unique b (carrier b) (inl b) (inr b)
>                         (composeCoProductMorphisms cat l r b a) in
>        rewrite unique b (carrier b) (inl b) (inr b)
>                         (idCommutingMorphism cat l r b) in Refl)
>
> BinaryCoProduct : Category -> Type
> BinaryCoProduct cat = (l, r : obj cat) -> CoProduct cat l r
