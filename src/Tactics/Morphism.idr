module Tactics.Morphism

-- The `morphism` tactic is defined here
-- Note that in general, idris's inference algorithm needs help with it, so use it either as
-- %runElab morphism
-- or
-- the (f = g) (%runElab morphism)

import Basic.Category
import Language.Reflection.Elab
import Pruviloj.Core

%language ElabReflection
%access public export

data MorphismExpr : (cat : Category) -> obj cat -> obj cat -> Type where
  IdExpr : (a : obj cat) -> MorphismExpr cat a a
  CompExpr : MorphismExpr cat a b -> MorphismExpr cat b c -> MorphismExpr cat a c
  OtherExpr : mor cat a b -> MorphismExpr cat a b

data MorphismPath : (cat : Category) -> obj cat -> obj cat -> Type where
  Nil : MorphismPath cat a a
  (::) : mor cat a b -> MorphismPath cat b c -> MorphismPath cat a c

(++) : MorphismPath cat a b -> MorphismPath cat b c -> MorphismPath cat a c
(++) [] q = q
(++) (f :: fs) q = f :: (fs ++ q)

unquoteExpr : MorphismExpr cat a b -> mor cat a b
unquoteExpr (IdExpr a) = identity _ a
unquoteExpr (CompExpr f g) = compose _ _ _ _ (unquoteExpr f) (unquoteExpr g)
unquoteExpr (OtherExpr f) = f

unquotePath : MorphismPath cat a b -> mor cat a b
unquotePath [] = identity _ _
unquotePath (f :: fs) = compose _ _ _ _ f (unquotePath fs)

-- does the "heavy lifting" by converting to a canonical form, e.g.:
-- assume f, g and h are morphisms
-- exprToPath (CompExpr (OtherExpr f) (CompExpr (OtherExpr g) (OtherExpr h))) = [f, g, h]
-- exprToPath (CompExpr (CompExpr (OtherExpr f) (OtherExpr g)) (OtherExpr h)) = [f, g, h]

exprToPath : MorphismExpr cat a b -> MorphismPath cat a b
exprToPath (IdExpr a) = []
exprToPath (CompExpr f g) = exprToPath f ++ exprToPath g
exprToPath (OtherExpr f) = [f]

unquotePathApp : (p : MorphismPath cat a b) -> (q : MorphismPath cat b c)
              -> unquotePath (p ++ q) = compose _ _ _ _ (unquotePath p) (unquotePath q)
unquotePathApp [] q = sym $ leftIdentity _ _ _ (unquotePath q)
unquotePathApp (f :: fs) q = rewrite unquotePathApp fs q in associativity _ _ _ _ _ _ _ _

unquoteTriangle : (f : MorphismExpr cat a b) -> unquotePath (exprToPath f) = unquoteExpr f
unquoteTriangle (IdExpr a) = Refl
unquoteTriangle (CompExpr f g) =
  rewrite unquotePathApp (exprToPath f) (exprToPath g) in
  rewrite unquoteTriangle f in
  rewrite unquoteTriangle g in Refl
unquoteTriangle (OtherExpr f) = rightIdentity _ _ _ _

proveEq : (f : MorphismExpr cat a b) -> (g : MorphismExpr cat a b)
       -> unquotePath (exprToPath f) = unquotePath (exprToPath g) -> unquoteExpr f = unquoteExpr g
proveEq f g hyp =
  rewrite sym $ unquoteTriangle f in
  rewrite sym $ unquoteTriangle g in hyp

reifyExpr : Raw -> Elab ()
reifyExpr `(identity ~cat ~a) = exact `(IdExpr {cat=~cat} ~a)
reifyExpr `(compose ~cat ~a ~b ~c ~f ~g) = do
  [l, r] <- refine `(CompExpr {cat=~cat} {a=~a} {b=~b} {c=~c})
  inHole l (reifyExpr f)
  inHole r (reifyExpr g) *> skip
reifyExpr tm = (refine (Var `{OtherExpr}) `andThen` exact tm) *> skip

morphism : Elab ()
morphism =
  case !(compute *> getGoal) of
    (_, `((=) {A=mor ~catl ~al ~bl} {B=mor ~catr ~ar ~br} ~e1 ~e2)) => do

      l <- gensym "L"
      r <- gensym "R"

      [catl', al', bl', catr', ar', br'] <- traverse forget [catl, al, bl, catr, ar, br]

      remember l `(MorphismExpr ~catl' ~al' ~bl'); reifyExpr !(forget e1)
      remember r `(MorphismExpr ~catr' ~ar' ~br'); reifyExpr !(forget e2)

      equiv `((=) {A=_} {B=_}
        (unquoteExpr {cat=~catl'} {a=~al'} {b=~bl'} ~(Var l))
        (unquoteExpr {cat=~catr'} {a=~ar'} {b=~br'} ~(Var r)))

      andThen (refine `(proveEq {cat=~catl'} {a=~al'} {b=~bl'} ~(Var l) ~(Var r))) reflexivity
      skip


test : (f : mor cat a b) -> (g : mor cat b c) -> (h : mor cat c d)
    -> compose _ _ _ _ f (compose _ _ _ _ g h) = compose _ _ _ _ (compose _ _ _ _ f g) h
test f g h = %runElab morphism
