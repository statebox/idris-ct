module CommutativeDiagram.Diagram

import Basic.Category
import Basic.Functor
import Preorder.PreorderAsCategory
import Preorder.UniquePreorder

public export
Diagram : Category -> Category -> Type
Diagram = CFunctor

public export
CommutativeDiagram : {t : Type}
                  -> {po : t -> t -> Type}
                  -> (preorder : UniquePreorder t po)
                  => Category
                  -> Type
CommutativeDiagram @{preorder} = Diagram (preorderAsCategory @{preorder})
