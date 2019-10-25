module Span.Span

import Basic.Category
import Basic.Functor
import CommutativeDiagram.Diagram
import Data.List
import Data.Vect
import Free.FreeFunctor
import Free.Graph
import Free.Path
import Free.PathCategory

public export
data SpanObject = X | Y | Z

public export
SpanGraph : Graph
SpanGraph = MkGraph
  SpanObject
  [(Z, X), (Z, Y)]

public export
SpanIndexCategory : Category
SpanIndexCategory = pathCategory SpanGraph

public export
Span : {cat : Category} -> (a, b : obj cat) -> Type
Span {cat} a b = (d : Diagram SpanIndexCategory cat ** e : (mapObj d X = a) ** mapObj d Y = b)

public export
spanFunctor : {cat : Category} -> {a, b : obj cat} -> Span {cat} a b -> CFunctor SpanIndexCategory cat
spanFunctor = fst

public export
span : {cat : Category}
    -> (x, y, z : obj cat)
    -> mor cat z x
    -> mor cat z y
    -> Span {cat} x y
span {cat} x y z f g = (freeFunctor {cat} SpanGraph graphEmbedding ** Refl ** Refl)
  where
    geObj : SpanObject -> obj cat
    geObj X = x
    geObj Y = y
    geObj Z = z

    geMor : (i, j : SpanObject) -> Edge SpanGraph i j -> mor cat (geObj i) (geObj j)
    geMor Z X Here         = f
    geMor Z Y (There Here) = g
    geMor X X Here         impossible
    geMor X X (There Here) impossible
    geMor X Y Here         impossible
    geMor X Y (There Here) impossible
    geMor X Z Here         impossible
    geMor X Z (There Here) impossible
    geMor Y X Here         impossible
    geMor Y X (There Here) impossible
    geMor Y Y Here         impossible
    geMor Y Y (There Here) impossible
    geMor Y Z Here         impossible
    geMor Y Z (There Here) impossible
    geMor Z X (There Here) impossible
    geMor Z Y Here         impossible
    geMor Z Z Here         impossible
    geMor Z Z (There Here) impossible

    graphEmbedding : GraphEmbedding SpanGraph cat
    graphEmbedding = MkGraphEmbedding geObj geMor