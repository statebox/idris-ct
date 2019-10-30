module Lens.Lens

import MonoidalCategory.MonoidalCategory
import Product.ProductCategory

public export
record Lens (s : Type) (t : Type) (a : Type) (b : Type) where
  constructor MkLens
  get : s -> a
  put : s -> b -> t

public export
eqLens : {l1, l2 : Lens s t a b}
      -> get l1 = get l2
      -> put l1 = put l2
      -> l1 = l2
eqLens _ _ = believe_me ()

public export
identityLens : Lens s t s t
identityLens = MkLens id (const id)

public export
lensComposition : Lens s t a b -> Lens a b c d  -> Lens s t c d
lensComposition outerLens innerLens = MkLens
  (get innerLens . get outerLens)
  (\s, d => put outerLens s (put innerLens (get outerLens s) d))

funExt : {f, g : a -> b}
      -> ((x : a) -> f x = g x)
      -> f = g
funExt prf = believe_me ()

public export
lensesAsCategory : Category
lensesAsCategory = MkCategory
  (Type, Type)
  (\st, ab => Lens (fst st) (snd st) (fst ab) (snd ab))
  (\st => identityLens {s = fst st} {t = snd st})
  (\_, _, _ => lensComposition)
  (\_, _, l => eqLens {l1=lensComposition l identityLens}
                      {l2=l}
                      (funExt (\x => Refl))
                      (funExt (\x => funExt {f=(\y => put l x y)} {g=put l x} (\y => Refl))))
  (\_, _, l => eqLens {l1=lensComposition identityLens l}
                      {l2=l}
                      (funExt (\x => Refl))
                      (funExt (\x => funExt {f=(\y => put l x y)} {g=put l x} (\y => Refl))))
  (\_, _, _, _, _, _, _ => Refl)