> module FreeMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Data.Fin
> import Discrete.DiscreteCategory
> import Monoid.FreeMonoid
> import Monoid.Monoid
> import MonoidalCategory.StrictMonoidalCategory
> import Product.ProductCategory
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
> finSetCategory : Nat -> Category
> finSetCategory n = discreteCategory (set $ finSetToFreeMonoid n)
>
> help : (ab : (List (Fin n), List (Fin n))) -> (cd : (List (Fin n), List (Fin n)))
>     -> ProductMorphism (finSetCategory n) (finSetCategory n) ab cd
>     -> fst ab ++ snd ab = fst cd ++ snd cd
> help (c, d) (c, d) (MkProductMorphism Refl Refl) = Refl
>
> finSetTensor : (n : Nat) -> CFunctor (productCategory (finSetCategory n) (finSetCategory n)) (finSetCategory n)
> finSetTensor n =
>   MkCFunctor
>     (\ab => fst ab ++ snd ab)
>     help
>     (\(a, b) => Refl)
>     (\(a, b), (c, d), (e, f), (MkProductMorphism Refl Refl), (MkProductMorphism Refl Refl) => Refl)
>
> help2 : (a, b, c, d, e, f : List (Fin n)) ->
>         (g : a = b) ->
>         (h : c = d) ->
>         (k : e = f) ->
>         help (a, c ++ e) (b, d ++ f) (MkProductMorphism g (help (c, e) (d, f) (MkProductMorphism h k))) =
>         help (a ++ c, e) (b ++ d, f) (MkProductMorphism (help (a, c) (b, d) (MkProductMorphism g h)) k)
> help2 {n} b b d d f f Refl Refl Refl = really_believe_me (Refl {x=Refl {x=b ++ d ++ f}})  -- TODO figure out how to rewrite appendAssociative
>
> finSetToFMC : Nat -> StrictMonoidalCategory
> finSetToFMC n = MkStrictMonoidalCategory
>                   (finSetCategory n)
>                   (finSetTensor n)
>                   []
>                   (\a => Refl)
>                   appendNilRightNeutral
>                   appendAssociative
>                   help2

> data Path : (i -> i -> Type) -> i -> i -> Type where
>  Nil  : Path e i i
>  (::) : e i j -> Path e j k -> Path e i k

 l_1...l_m
 ()
a   b

generatorsToCat : (n:Nat) -> List ((Fin n, Fin n)) -> Category
generatorsToCat n gs =
  MkCategory
    (Fin n)
    (\m,p => Path ())
    ?ident
    ?comp
    ?lid
    ?rid
    ?assoc

 generatorsToFMC : (n:Nat) -> List ((finSetToFreeMonoid n, finSetToFreeMonoid n)) -> StrictMonoidalCategory
 generatorsToFMC n gs =
   MkStrictMonoidalCategory
     (finSetToFreeMonoid n)
     ?wat
