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

> module MonoidalCategory.FreeMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Data.List
> import Monoid.FreeMonoid
> import Monoid.Monoid
> import MonoidalCategory.StrictMonoidalCategory
> import MonoidalCategory.StrictSymmetricMonoidalCategory
> import MonoidalCategory.SymmetricMonoidalCategoryHelpers
> import Product.ProductCategory
>
> %access export -- we do not default to public so that we don't leak implementation details
> %default total
>
> -- define privately the data type with its generators
> private
> data PreFreeMorphism :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> (domain : List t)
>   -> (codomain : List t)
>   -> Type
> where
>   MkIdFreeMorphism            : (x : List t) -> PreFreeMorphism t generatingMorphisms x x
>   MkSymmetryFreeMorphism      : (x, y : List t) -> PreFreeMorphism t generatingMorphisms (x ++ y) (y ++ x)
>   MkCompositionFreeMorphism   : PreFreeMorphism t generatingMorphisms a b
>                              -> PreFreeMorphism t generatingMorphisms b c
>                              -> PreFreeMorphism t generatingMorphisms a c
>   MkJuxtapositionFreeMorphism : PreFreeMorphism t generatingMorphisms a b
>                              -> PreFreeMorphism t generatingMorphisms c d
>                              -> PreFreeMorphism t generatingMorphisms (a ++ c) (b ++ d)
>   MkGeneratingFreeMorphism    : (e : (List t, List t))
>                              -> Elem e generatingMorphisms
>                              -> PreFreeMorphism t generatingMorphisms (Basics.fst e) (Basics.snd e)
>
> -- define the real data type which will represent the quotient
> -- it gives no access to its constructors, so that we can limit the functions which are definable on it
> FreeMorphism :
>      (t : Type)
>   -> (generatingMorphisms : List (List t, List t))
>   -> (domain : List t)
>   -> (codomain : List t)
>   -> Type
> FreeMorphism = PreFreeMorphism
>
> -- provide smart constructors to replicate the constructors of the non-quotiented version
> idFreeMorphism : (x : List t) -> FreeMorphism t generatingMorphisms x x
> idFreeMorphism = MkIdFreeMorphism
>
> symmetryFreeMorphism : (x, y : List t) -> FreeMorphism t generatingMorphisms (x ++ y) (y ++ x)
> symmetryFreeMorphism = MkSymmetryFreeMorphism
>
> compositionFreeMorphism :
>      FreeMorphism t generatingMorphisms a b
>   -> FreeMorphism t generatingMorphisms b c
>   -> FreeMorphism t generatingMorphisms a c
> compositionFreeMorphism = MkCompositionFreeMorphism
>
> juxtapositionFreeMorphism :
>      FreeMorphism t generatingMorphisms a b
>   -> FreeMorphism t generatingMorphisms c d
>   -> FreeMorphism t generatingMorphisms (a ++ c) (b ++ d)
> juxtapositionFreeMorphism = MkJuxtapositionFreeMorphism
>
> generatingFreeMorphism :
>      (e : (List t, List t))
>   -> Elem e generatingMorphisms
>   -> FreeMorphism t generatingMorphisms (Basics.fst e) (Basics.snd e)
> generatingFreeMorphism = MkGeneratingFreeMorphism
>
> freeIdentity : (ts : List t) -> FreeMorphism t generatingMorphisms ts ts
> freeIdentity = idFreeMorphism
>
> freeComposition :
>      (as, bs, cs : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> FreeMorphism t generatingMorphisms as cs
> freeComposition as bs cs fm1 fm2 = compositionFreeMorphism fm1 fm2
>
> postulate
> freeLeftIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> compositionFreeMorphism (freeIdentity as) fm = fm
>
> postulate
> freeRightIdentity :
>      (as, bs : List t)
>   -> (fm : FreeMorphism t generatingMorphisms as bs)
>   -> compositionFreeMorphism fm (freeIdentity bs) = fm
>
> postulate
> freeAssociativity :
>      (as, bs, cs, ds : List t)
>   -> (fm1 : FreeMorphism t generatingMorphisms as bs)
>   -> (fm2 : FreeMorphism t generatingMorphisms bs cs)
>   -> (fm3 : FreeMorphism t generatingMorphisms cs ds)
>   -> compositionFreeMorphism fm1 (compositionFreeMorphism fm2 fm3)
>    = compositionFreeMorphism (compositionFreeMorphism fm1 fm2) fm3
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
> freeTensorMorphism a b (MkProductMorphism f1 f2) = juxtapositionFreeMorphism f1 f2
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
>   -> juxtapositionFreeMorphism g (juxtapositionFreeMorphism h k)
>    = juxtapositionFreeMorphism (juxtapositionFreeMorphism g h) k
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
>   -> compositionFreeMorphism (symmetryFreeMorphism a b) (juxtapositionFreeMorphism g f)
>    = compositionFreeMorphism (juxtapositionFreeMorphism f g) (symmetryFreeMorphism c d)
>
> private
> freeSymmetryCommutativity :
>      (a, b : (List t, List t))
>   -> (f : ProductMorphism (generateFreeCategory t generatingMorphisms)
>                           (generateFreeCategory t generatingMorphisms)
>                           a b)
>   -> let freeCat = (generateFreeCategory t generatingMorphisms)
>      in  freeComposition (mapObj (freeTensor t generatingMorphisms) a)
>                          (mapObj (functorComposition (productCategory freeCat freeCat)
>                                                      (productCategory freeCat freeCat)
>                                                      freeCat
>                                                      (swapFunctor freeCat freeCat)
>                                                      (freeTensor t generatingMorphisms))
>                                  a)
>                          (mapObj (functorComposition (productCategory freeCat freeCat)
>                                                      (productCategory freeCat freeCat)
>                                                      freeCat
>                                                      (swapFunctor freeCat freeCat)
>                                                      (freeTensor t generatingMorphisms))
>                                  b)
>                          (rewrite sym (swapConcat a) in symmetryFreeMorphism (fst a) (snd a))
>                          (mapMor (functorComposition (productCategory freeCat freeCat)
>                                                      (productCategory freeCat freeCat)
>                                                      freeCat
>                                                      (swapFunctor freeCat freeCat)
>                                                      (freeTensor t generatingMorphisms))
>                                  a b f)
>    = freeComposition (mapObj (freeTensor t generatingMorphisms) a)
>                      (mapObj (freeTensor t generatingMorphisms) b)
>                      (mapObj (functorComposition (productCategory freeCat freeCat)
>                                                  (productCategory freeCat freeCat)
>                                                  freeCat
>                                                  (swapFunctor freeCat freeCat)
>                                                  (freeTensor t generatingMorphisms))
>                              b)
>                      (mapMor (freeTensor t generatingMorphisms) a b f)
>                      (rewrite sym (swapConcat b) in symmetryFreeMorphism (fst b) (snd b))
> freeSymmetryCommutativity (a1, a2) (b1, b2) (MkProductMorphism f1 f2) = freeTensorPreserveSwap a1 a2 b1 b2 f1 f2
>
> postulate
> freeSymmetryIsInvolution :
>      (a, b : List t)
>   -> compositionFreeMorphism (symmetryFreeMorphism a b) (symmetryFreeMorphism b a)
>    = idFreeMorphism (a ++ b)
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
>   (MkNaturalTransformation (\a => rewrite sym (swapConcat a) in symmetryFreeMorphism (fst a) (snd a))
>                            (\a, b, f => freeSymmetryCommutativity a b f))
>   (\(a1, a2) => MkIsomorphism (symmetryFreeMorphism a2 a1)
>                               (freeSymmetryIsInvolution a1 a2)
>                               (freeSymmetryIsInvolution a2 a1))
>
> postulate
> freeUnitCoherence :
>      (a : List t)
>   -> symmetryFreeMorphism a []
>    = idFreeMorphism a
>
> postulate
> freeAssociativityCoherence :
>      (a, b, c : List t)
>   -> symmetryFreeMorphism a (b ++ c)
>    = compositionFreeMorphism (juxtapositionFreeMorphism (symmetryFreeMorphism a b) (idFreeMorphism c))
>                              (rewrite__impl (\r => FreeMorphism t generatingMorphisms r ((b ++ c) ++ a))
>                                             (sym (appendAssociative b a c))
>                                             (rewrite__impl (\r => FreeMorphism t generatingMorphisms (b ++ a ++ c) r)
>                                                            (sym (appendAssociative b c a))
>                                                            (juxtapositionFreeMorphism (idFreeMorphism b)
>                                                                                       (symmetryFreeMorphism a c))))
>
> generateFreeSymmetricMonoidalCategory : (t : Type) -> List (List t, List t) -> StrictSymmetricMonoidalCategory
> generateFreeSymmetricMonoidalCategory t generatingMorphisms = MkStrictSymmetricMonoidalCategory
>   (generateFreeMonoidalCategory t generatingMorphisms)
>   (freeSymmetry t generatingMorphisms)
>   (\a => freeUnitCoherence a)
>   (\a, b, c => freeAssociativityCoherence a b c)
>   (\a, b => freeSymmetryIsInvolution a b)
>
> foldOnMorphisms :
>      {ssmc : StrictSymmetricMonoidalCategory}
>   -> (onObj : List t -> obj (cat (smcat ssmc)))
>   -> (onGeneratingMor :
>           (f : (List t, List t))
>        -> (Elem f generatingMorphisms)
>        -> mor (cat (smcat ssmc)) (onObj $ fst f) (onObj $ snd f))
>   -> (a, b : List t)
>   -> mor (cat (smcat (generateFreeSymmetricMonoidalCategory t generatingMorphisms))) a b
>   -> mor (cat (smcat ssmc)) (onObj a) (onObj b)
> foldOnMorphisms {ssmc} onObj onGeneratingMor a a (MkIdFreeMorphism a) =
>   identity (cat (smcat ssmc)) (onObj a)
> foldOnMorphisms {ssmc} onObj onGeneratingMor (a ++ b) (b ++ a) (MkSymmetryFreeMorphism a b) =
>   component (natTrans (symmetry ssmc)) (onObj a, onObj b)
> foldOnMorphisms {ssmc} onObj onGeneratingMor a b (MkCompositionFreeMorphism g1 g2) =
>   compose (cat (smcat ssmc)) _ _ _ g1 g2
> foldOnMorphisms {ssmc} onObj onGeneratingMor (a ++ c) (b ++ d) (MkJuxtapositionFreeMorphism g1 g2) =
>   mapMor (tensor (smcat ssmc)) _ _ (MkProductMorphism g1 g2)
> foldOnMorphisms {ssmc} onObj onGeneratingMor (fst genMor) (snd genMor) (MkGeneratingFreeMorphism genMor prf) =
>   onGeneratingMor genMor prf
>
> -- elimination rule for FreeMorphism
> fold :
>      {ssmc : StrictSymmetricMonoidalCategory}
>   -> (onObj : List t -> obj (cat (smcat ssmc)))
>   -> (onGeneratingMor :
>           (f : (List t, List t))
>        -> (Elem f generatingMorphisms)
>        -> mor (cat (smcat ssmc)) (onObj $ fst f) (onObj $ snd f))
>   -- TODO: this should really be a symmetric monoidal functor
>   -> CFunctor (cat (smcat (generateFreeSymmetricMonoidalCategory t generatingMorphisms)))
>               (cat (smcat ssmc))
> fold {ssmc} onObj onGeneratingMor = MkCFunctor
>   onObj
>   (foldOnMorphisms {ssmc} onObj onGeneratingMor)
>   (\a => ?preserveId)
>   ?preserveComposition
