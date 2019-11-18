module Free.FreeFunctor

import Basic.Category
import Basic.Functor
import Data.List
import Free.Graph
import Free.Path
import Free.PathCategory

public export
record GraphEmbedding (g : Graph) (cat : Category) where
  constructor MkGraphEmbedding
  mapVertices : vertices g -> obj cat
  mapEdges    : {0 i, j : vertices g} -> Edge g i j -> mor cat (mapVertices i) (mapVertices j)

public export
foldPath :
     (g : Graph)
  -> {cat : Category}
  -> (ge : GraphEmbedding g cat)
  -> {i, j : vertices g}
  -> Path g i j
  -> mor cat (mapVertices ge i) (mapVertices ge j)
foldPath _ ge []        = identity cat (mapVertices ge i)
foldPath g ge (x :: xs) = compose cat _ _ _ (mapEdges ge x) (foldPath g ge xs)

public export
freeFunctorCompose :
     (g : Graph)
  -> (ge : GraphEmbedding g cat)
  -> (i, j, k : vertices g)
  -> (f : Path g i j)
  -> (h : Path g j k)
  -> foldPath g ge {j = k} (joinPath f h)
   = compose cat
             (mapVertices ge i)
             (mapVertices ge j)
             (mapVertices ge k)
             (foldPath g ge f)
             (foldPath g ge {i = j} {j = k} h)
freeFunctorCompose g ge j j k []        h =
  sym $ leftIdentity cat
    (mapVertices ge j)
    (mapVertices ge k)
    (foldPath g ge h)
freeFunctorCompose g ge i j k (x :: xs) h =
  trans (cong (compose cat _ _ _ (mapEdges ge x)) $ freeFunctorCompose g ge _ _ _ xs h)
        (associativity cat _ _ _ _ (mapEdges ge x) (foldPath g ge xs) (foldPath g ge h))

public export
freeFunctor : (g : Graph)   -> {cat : Category}-> GraphEmbedding g cat -> CFunctor (pathCategory g) cat
freeFunctor g@(MkGraph _ _) ge@(MkGraphEmbedding mapV _) =
  MkCFunctor
    mapV
    (\i, j, p => foldPath g ge {i} {j} p)
    (\_ => Refl)
    (freeFunctorCompose g ge)
