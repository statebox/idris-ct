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
      -> ((x : s) -> get l1 x = get l2 x)
      -> ((x : s) -> (y : b) -> put l1 x y = put l2 x y)
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

public export
lensesAsCategory : Category
lensesAsCategory = MkCategory
  (Type, Type)
  (\st, ab => Lens (fst st) (snd st) (fst ab) (snd ab))
  (\st => identityLens {s = fst st} {t = snd st})
  (\_, _, _ => lensComposition)
  (\_, _, l => eqLens {l1=lensComposition l identityLens}
                      {l2=l}
                      (\x => Refl)
                      (\x, y => Refl))
  (\_, _, l => eqLens {l1=lensComposition identityLens l}
                      {l2=l}
                      (\x => Refl)
                      (\x, y => Refl))
  (\_, _, _, _, _, _, _ => Refl)