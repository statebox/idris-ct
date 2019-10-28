module CoLimits.CoCone

import Basic.Category
import Basic.ConstantFunctor
import Basic.Functor
import Basic.NaturalTransformation
import CommutativeDiagram.Diagram

public export
CoCone : {index, cat : Category}
      -> (diagram : Diagram index cat)
      -> (n : obj cat)
      -> Type
CoCone {index} {cat} diagram n = NaturalTransformation index cat diagram (Delta index cat n)

public export
record CoConeMorphism
  (index : Category) (cat : Category)
  (diagram : Diagram index cat)
  (a: obj cat) (b : obj cat)
  (source : CoCone {index} {cat} diagram a) (target : CoCone {index} {cat} diagram b)
where
  constructor MkCoConeMorphism
  apexMorphism  : mor cat a b
  commutativity : (i : obj index)
               -> compose cat (mapObj diagram i) a b (component {fun2=Delta index cat a} source i) apexMorphism
                = component {fun2=Delta index cat b} target i
