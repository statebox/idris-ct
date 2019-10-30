module Lens.SimpleLens

import Basic.Category
import Lens.Lens

public export
SimpleLens : Type -> Type -> Type
SimpleLens s a = Lens s s a a

public export
simpleLensesAsCategory : Category
simpleLensesAsCategory = MkCategory
  Type
  SimpleLens
  (\s => identityLens {s = s} {t = s})
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