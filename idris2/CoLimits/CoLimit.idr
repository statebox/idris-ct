module CoLimits.CoLimit

import Basic.Category
import CoLimits.CoCone
import CommutativeDiagram.Diagram

public export
record CoLimit
  (index   : Category)
  (cat     : Category)
  (diagram : Diagram index cat)
where
  constructor MkCoLimit
  carrier: obj cat
  cocone: CoCone diagram carrier
  exists:
       (apexB : obj cat)
    -> (b : CoCone diagram apexB)
    -> CoConeMorphism index cat diagram carrier apexB cocone b
  unique:
       (apexB : obj cat)
    -> (b : CoCone diagram apexB)
    -> (f, g : CoConeMorphism index cat diagram carrier apexB cocone b)
    -> f = g
