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

> module FreeMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Data.List
> import Data.Fin
> import Discrete.DiscreteCategory
> import Monoid.FreeMonoid
> import Monoid.Monoid
> import MonoidalCategory.StrictMonoidalCategory
> import MonoidalCategory.StrictSymmetricMonoidalCategory
> import MonoidalCategory.SymmetricMonoidalCategoryHelpers
> import Product.ProductCategory
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> data FreeMorphism :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> (domain : List t)
>   -> (codomain : List t)
>   -> Type
> where
>   MkIdFreeMorphism            : (x : List t) -> FreeMorphism t generatingMorphisms x x
>   MkSymmetryFreeMorphism      : (x, y : List t) -> FreeMorphism t generatingMorphisms (x ++ y) (y ++ x)
>   MkCompositionFreeMorphism   : FreeMorphism t generatingMorphisms a b
>                              -> FreeMorphism t generatingMorphisms b c
>                              -> FreeMorphism t generatingMorphisms a c
>   MkJuxtapositionFreeMorphism : FreeMorphism t generatingMorphisms a b
>                              -> FreeMorphism t generatingMorphisms c d
>                              -> FreeMorphism t generatingMorphisms (a ++ c) (b ++ d)
>   MkGeneratingFreeMorphism    : (l : List (List t, List t))
>                              -> (e : (List t, List t))
>                              -> Elem e l
>                              -> FreeMorphism t l (Basics.fst e) (Basics.snd e)
>
> freeIdentity : (ts : List t) -> FreeMorphism t generatingMorphisms ts ts
> freeIdentity = MkIdFreeMorphism
>
> freeComposition :
>      (as, bs, cs : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> FreeMorphism t generatingMorphisms as cs
> freeComposition as bs cs fm1 fm2 = MkCompositionFreeMorphism fm1 fm2
>
> postulate
> freeLeftIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> MkCompositionFreeMorphism (freeIdentity as) fm = fm
>
> postulate
> freeRightIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> MkCompositionFreeMorphism fm (freeIdentity bs) = fm
>
> postulate
> freeAssociativity :
>      (as, bs, cs, ds : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> (fm3 : FreeMorphism t generatingMorphisms cs ds)
>   -> MkCompositionFreeMorphism fm1 (MkCompositionFreeMorphism fm2 fm3)
>    = MkCompositionFreeMorphism (MkCompositionFreeMorphism fm1 fm2) fm3
>
> generateFreeCategory : (t : Type) -> List (List t, List t) -> Category
> generateFreeCategory t generatingMorphisms =
>   MkCategory
>     (List t)
>     (FreeMorphism t generatingMorphisms)
>     freeIdentity
>     freeComposition
>     freeLeftIdentity
>     freeRightIdentity
>     freeAssociativity
>
> freeTensorObject : (List t, List t) -> List t
> freeTensorObject pair = fst pair ++ snd pair
>
> freeTensorMorphism :
>      (a, b : (List t, List t))
>   -> ProductMorphism (generateFreeCategory t generatingMorphisms)
>                      (generateFreeCategory t generatingMorphisms)
>                      a b
>   -> FreeMorphism t generatingMorphisms (fst a ++ snd a) (fst b ++ snd b)
> freeTensorMorphism a b (MkProductMorphism f1 f2) = MkJuxtapositionFreeMorphism f1 f2
>
> postulate
> freeTensorPreserveId :
>      (a : (List t, List t))
>   -> freeTensorMorphism a a (MkProductMorphism (freeIdentity (fst a)) (freeIdentity (snd a)))
>    = freeIdentity (freeTensorObject a)
>
> postulate
> freeTensorPreserveCompose :
>      (a, b, c : (List t, List t))
>   -> (f : ProductMorphism (generateFreeCategory t generatingMorphisms)
>                           (generateFreeCategory t generatingMorphisms)
>                           a b)
>   -> (g : ProductMorphism (generateFreeCategory t generatingMorphisms)
>                           (generateFreeCategory t generatingMorphisms)
>                           b c)
>   -> freeTensorMorphism a c (productCompose a b c f g)
>    = freeComposition (freeTensorObject a)
>                      (freeTensorObject b)
>                      (freeTensorObject c)
>                      (freeTensorMorphism a b f)
>                      (freeTensorMorphism b c g)
>
> freeTensor :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> CFunctor (productCategory (generateFreeCategory t generatingMorphisms)
>                                (generateFreeCategory t generatingMorphisms))
>               (generateFreeCategory t generatingMorphisms)
> freeTensor t generatingMorphisms = MkCFunctor
>   freeTensorObject
>   freeTensorMorphism
>   freeTensorPreserveId
>   freeTensorPreserveCompose
>
> postulate
> freeTensorAssociative :
>      (a, b, c, d, e, f : List t)
>   -> (g : FreeMorphism t generatingMorphisms a b)
>   -> (h : FreeMorphism t generatingMorphisms c d)
>   -> (k : FreeMorphism t generatingMorphisms e f)
>   -> MkJuxtapositionFreeMorphism g (MkJuxtapositionFreeMorphism h k)
>    = MkJuxtapositionFreeMorphism (MkJuxtapositionFreeMorphism g h) k
>
> generateFreeMonoidalCategory : (t : Type) -> List (List t, List t) -> StrictMonoidalCategory
> generateFreeMonoidalCategory t generatingMorphisms = MkStrictMonoidalCategory
>   (generateFreeCategory t generatingMorphisms)
>   (freeTensor t generatingMorphisms)
>   []
>   (\a => Refl)
>   appendNilRightNeutral
>   appendAssociative
>   freeTensorAssociative
>
> swapConcat : (x : (List t, List t)) -> snd x ++ fst x = fst (swap x) ++ snd (swap x)
> swapConcat (x1, x2) = Refl
>
> postulate
> freeTensorPreserveSwap :
>      (a, b, c, d : List t)
>   -> (f : FreeMorphism t generatingMorphisms a c)
>   -> (g : FreeMorphism t generatingMorphisms b d)
>   -> MkCompositionFreeMorphism (MkSymmetryFreeMorphism a b) (MkJuxtapositionFreeMorphism g f)
>    = MkCompositionFreeMorphism (MkJuxtapositionFreeMorphism f g) (MkSymmetryFreeMorphism c d)
>
> freeSymmetryCommutativity :
>      (a, b : (List t, List t))
>   -> (f : ProductMorphism (generateFreeCategory t generatingMorphisms) (generateFreeCategory t generatingMorphisms) a b)
>   -> compose (generateFreeCategory t generatingMorphisms)
>              (mapObj (freeTensor t generatingMorphisms) a)
>              (mapObj (functorComposition (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (generateFreeCategory t generatingMorphisms)
>                                             (swapFunctor (generateFreeCategory t generatingMorphisms)
>                                                          (generateFreeCategory t generatingMorphisms))
>                                             (freeTensor t generatingMorphisms)) a)
>              (mapObj (functorComposition (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (generateFreeCategory t generatingMorphisms)
>                                             (swapFunctor (generateFreeCategory t generatingMorphisms)
>                                                          (generateFreeCategory t generatingMorphisms))
>                                             (freeTensor t generatingMorphisms)) b)
>              (rewrite sym (swapConcat a) in MkSymmetryFreeMorphism (fst a) (snd a))
>              (mapMor (functorComposition (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (generateFreeCategory t generatingMorphisms)
>                                             (swapFunctor (generateFreeCategory t generatingMorphisms)
>                                                          (generateFreeCategory t generatingMorphisms))
>                                             (freeTensor t generatingMorphisms)) a b f)
>    = compose (generateFreeCategory t generatingMorphisms)
>              (mapObj (freeTensor t generatingMorphisms) a)
>              (mapObj (freeTensor t generatingMorphisms) b)
>              (mapObj (functorComposition (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (generateFreeCategory t generatingMorphisms)
>                                             (swapFunctor (generateFreeCategory t generatingMorphisms)
>                                                          (generateFreeCategory t generatingMorphisms))
>                                             (freeTensor t generatingMorphisms)) b)
>              (mapMor (freeTensor t generatingMorphisms) a b f)
>              (rewrite sym (swapConcat b) in MkSymmetryFreeMorphism (fst b) (snd b))
> freeSymmetryCommutativity (a1, a2) (b1, b2) (MkProductMorphism f1 f2) = freeTensorPreserveSwap a1 a2 b1 b2 f1 f2
>
> postulate
> freeSymmetryIsInvolution :
>      (a, b : List t)
>   -> MkCompositionFreeMorphism (MkSymmetryFreeMorphism a b) (MkSymmetryFreeMorphism b a)
>    = MkIdFreeMorphism (a ++ b)
>
> freeSymmetry :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> NaturalIsomorphism (productCategory (generateFreeCategory t generatingMorphisms)
>                                          (generateFreeCategory t generatingMorphisms))
>                         (generateFreeCategory t generatingMorphisms)
>                         (freeTensor t generatingMorphisms)
>                         (functorComposition (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (productCategory (generateFreeCategory t generatingMorphisms)
>                                                              (generateFreeCategory t generatingMorphisms))
>                                             (generateFreeCategory t generatingMorphisms)
>                                             (swapFunctor (generateFreeCategory t generatingMorphisms)
>                                                          (generateFreeCategory t generatingMorphisms))
>                                             (freeTensor t generatingMorphisms))
> freeSymmetry t generatingMorphisms = MkNaturalIsomorphism
>   (MkNaturalTransformation (\a => rewrite sym (swapConcat a) in MkSymmetryFreeMorphism (fst a) (snd a))
>                            (\a, b, f => freeSymmetryCommutativity a b f))
>   (\(a1, a2) => MkIsomorphism (MkSymmetryFreeMorphism a2 a1)
>                               (freeSymmetryIsInvolution a1 a2)
>                               (freeSymmetryIsInvolution a2 a1))
>
> postulate
> freeUnitCoherence :
>      (a : List t)
>   -> MkSymmetryFreeMorphism a []
>    = MkIdFreeMorphism a
>
> postulate
> freeAssociativityCoherence :
>      (a, b, c : List t)
>   -> MkSymmetryFreeMorphism a (b ++ c)
>    = MkCompositionFreeMorphism (MkJuxtapositionFreeMorphism (MkSymmetryFreeMorphism a b) (MkIdFreeMorphism c))
>                                (rewrite (sym (appendAssociative b a c)) in
>                                         (rewrite__impl (\r => FreeMorphism t generatingMorphisms (b ++ a ++ c) r)
>                                                        (sym (appendAssociative b c a))
>                                                        (MkJuxtapositionFreeMorphism (MkIdFreeMorphism b)
>                                                                                     (MkSymmetryFreeMorphism a c))))
>
> generateFreeSymmetricMonoidalCategory : (t : Type) -> List (List t, List t) -> StrictSymmetricMonoidalCategory
> generateFreeSymmetricMonoidalCategory t generatingMorphisms = MkStrictSymmetricMonoidalCategory
>   (generateFreeMonoidalCategory t generatingMorphisms)
>   (freeSymmetry t generatingMorphisms)
>   (\a => freeUnitCoherence a)
>   (\a, b, c => freeAssociativityCoherence a b c)
>   (\a, b => freeSymmetryIsInvolution a b)
