> module Free.Category
>
> import Basic.Category
>
> %access public export
> %default total
>
> record Graph where
>   constructor MkGraph
>   Vert : Type
>   Edge : Vert -> Vert -> Type
>
> ||| IDRIS MAGIC a :: b :: c :: Nil = [a,b,c]
> data Path : (e : t -> t -> Type) -> t -> t -> Type where
>   Nil  : Path e i i
>   (::) : e i j -> Path e j k -> Path e i k
>
> edgeToPath : {g : Graph} -> Edge g i j -> Path (Edge g) i j
> edgeToPath e = [e]
>
> joinPath : {e : t -> t -> Type} -> Path e i j -> Path e j k -> Path e i k
> joinPath []      y = y
> joinPath (x::xs) y = x :: joinPath xs y
> 
> joinPathNil : (p : Path e i j) -> joinPath p [] = p
> joinPathNil Nil = Refl
> joinPathNil (eij :: p) = cong $ joinPathNil p
>
> joinPathAssoc : (p : Path e i j) -> (q : Path e j k) -> (r : Path e k l) -> 
>                  joinPath p (joinPath q r) = joinPath (joinPath p q) r
> joinPathAssoc Nil q r = Refl
> joinPathAssoc (eij::p) q r = cong $ joinPathAssoc p q r
>
> pathCategory : Graph -> Category
> pathCategory (MkGraph v e) = MkCategory v (Path e) (\a => Nil) (\a,b,c,f,g => joinPath f g)
>    (\a,b,f => Refl) (\a,b,f => joinPathNil f) (\a,b,c,d,f,g,h => joinPathAssoc f g h) 
