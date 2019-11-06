module Free.Graph

import Data.List.Elem

public export
record Graph where
  constructor MkGraph
  vertices : Type
  edges    : List (vertices, vertices)

public export
Edge : (g : Graph) -> (i, j : vertices g) -> Type
Edge (MkGraph _ e) v1 v2 = Elem (v1, v2) e

-- TODO do we really need these?
public export
edgeOrigin : {i : vertices g} -> {0 j : vertices g} -> Edge g i j -> vertices g
edgeOrigin _ = i

public export
edgeTarget : {0 i : vertices g} -> {j : vertices g} -> Edge g i j -> vertices g
edgeTarget _ = j

-- data TriangleVertices = One | Two | Three
--
-- triangle : Graph
-- triangle = MkGraph TriangleVertices [(One, Two), (Two, Three), (Three, One)]
