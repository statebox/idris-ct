
module DiscreteFunctors


import Basic.Category
import Basic.Functor
import Discrete.DiscreteCategory

%default total

infixr 6 ||>

(||>) : CFunctor a b -> CFunctor b c -> CFunctor a c
(||>) {a} {b} {c} lhs rhs = Basic.Functor.functorComposition a b c lhs rhs

infixr 5 -*>

(-*>) : Type -> Type -> Type
(-*>) lhs rhs = CFunctor (discreteCategory lhs) (discreteCategory rhs)

discreteMor : (f : a -> b) -> (v1, v2 : a) 
           -> DiscreteMorphism v1 v2 -> DiscreteMorphism (f v1) (f v2)
discreteMor f v1 v2 mor = cong {f=f} mor

discreteComp : (fn : a -> b) -> (v1, v2, v3 : a) ->
               (f : v1 = v2) ->
               (g : v2 = v3) ->
               cong (discreteCompose v1 v2 v3 f g) =
               discreteCompose (fn v1) (fn v2) (fn v3) (cong f) (cong g)

DiscreteFunctor : (a -> b) -> a -*> b
DiscreteFunctor f = MkCFunctor
  f
  (discreteMor f)
  (\_ => Refl)
  (discreteComp f)

execute : a -*> b -> a -> b
execute f val = mapObj f val

-- TypeCat but using Discrete functors instead of TypeMorphisms

typeCatId : (a : Type) ->  a -*> a
typeCatId a = DiscreteFunctor (\a => a)

typeCatLeftId : (a, b : Type) -> (f : a -*> b) -> typeCatId a ||> f = f

typeCatRightId : (a, b : Type) -> (f : a -*> b) -> f ||> typeCatId b = f

typeCatAssoc : (a, b, c, d : Type)
            -> (f : a -*> b)
            -> (g : b -*> c)
            -> (h : c -*> d)
            -> f ||> (g ||> h) = (f ||> g) ||> h

typeCatAsNaturalTransformation : Category
typeCatAsNaturalTransformation = MkCategory
  Type
  (-*>)
  typeCatId
  (\_, _, _ => (||>))
  typeCatLeftId
  typeCatRightId
  typeCatAssoc

askForInput : () -> IO String
askForInput () = getLine

printText : String -> IO ()
printText text = putStrLn $ "you wrote: " ++ text

askAndPrint : () -> IO ()
askAndPrint () = askForInput () >>= printText

liftedAskAndPrint : () -*> IO ()
liftedAskAndPrint = DiscreteFunctor (askAndPrint)

partial
forever : IO b -> IO b
forever a = do a; forever a

partial
liftLoop : a -*> IO b -> a -*> IO b
liftLoop computation = DiscreteFunctor (\a => forever (mapObj computation a))

