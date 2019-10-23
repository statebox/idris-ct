module Free.PathCategory

import Basic.Category
import Free.Graph
import Free.Path

public export
pathCategory : Graph -> Category
pathCategory g@(MkGraph v e) = MkCategory
  v
  (Path g)
  (\_ => Nil)
  (\_, _, _, f, g => joinPath f g)
  (\_, _, _ => Refl)
  (\_, _, f => joinPathNil f)
  (\_, _, _, _, f, g, h => joinPathAssoc f g h)