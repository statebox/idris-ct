> module Free.Functor
>
> import Basic.Category
> import Basic.Functor
> import Free.Category
>
> %access public export
> %default total
>
> forgetCat : Category -> Graph
> forgetCat c = MkGraph (obj c) (mor c)
>
> record GraphMorphism (g1 : Graph) (g2 : Graph) where
>   constructor MkGraphMorphism
>   mapVert : Vert g1 -> Vert g2
>   mapEdge : (v1, v2 : Vert g1) -> Edge g1 v1 v2 -> Edge g2 (mapVert v1) (mapVert v2)
>
> foldPath : (g : Graph) -> (gm : GraphMorphism g (forgetCat c)) -> Path (Edge g) a b -> mor c (mapVert gm a) (mapVert gm b)
> foldPath {c} {a} g gm Nil = identity c (mapVert gm a)
> foldPath {c}     g gm (eij :: p)     = compose c _ _ _ (mapEdge gm _ _ eij) (foldPath g gm p)
>
> freeFunctor : (g : Graph) -> (c : Category) -> GraphMorphism g (forgetCat c) -> CFunctor (pathCategory g) c
> freeFunctor (MkGraph v e) c gm = MkCFunctor (mapVert gm) (\a, b, p => foldPath {c} (MkGraph v e) gm p) (\_ => Refl) preserveComp
>   where
>   preserveComp : (x, y, z : v) -> (f : Path e x y) -> (g : Path e y z) -> foldPath (MkGraph v e) gm (joinPath f g) =
>                compose c (mapVert gm x) (mapVert gm y) (mapVert gm z) (foldPath (MkGraph v e) gm f) (foldPath (MkGraph v e) gm g)
>   preserveComp y y z Nil g = sym $ leftIdentity c (mapVert gm y) (mapVert gm z) (foldPath (MkGraph v e) gm g)
>   preserveComp x y z (fab::f) g = rewrite preserveComp _ _ _ f g in associativity c _ _ _ _ (mapEdge gm x _ fab) (foldPath (MkGraph v e) gm f) (foldPath (MkGraph v e) gm g)
>
