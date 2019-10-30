module Lens.SimpleLens

import Basic.Category
import Lens.Lens

public export
SimpleLens : Type -> Type -> Type
SimpleLens s a = Lens s s a a

funExt : {f, g : a -> b}
      -> ((x : a) -> f x = g x)
      -> f = g
funExt prf = believe_me ()

public export
simpleLensesAsCategory : Category
simpleLensesAsCategory = MkCategory
  Type
  SimpleLens
  (\s => identityLens {s = s} {t = s})
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