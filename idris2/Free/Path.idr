module Free.Path

import Data.List.Elem
import Free.Graph

public export
data Path : (g : Graph) -> vertices g -> vertices g -> Type where
   Nil  : Path g i i
   (::) : {i, j : vertices g} -> Edge g i j -> Path g j k -> Path g i k

-- nullPath : Path Graph.triangle One One
-- nullPath = Nil
--
-- oneToThree : Path Graph.triangle One Three
-- oneToThree = [Here, There Here]
--
-- oneToThree' : Path Graph.triangle One Three
-- oneToThree' = Here :: There Here :: Nil

public export
edgeToPath : {i, j : vertices g} -> Edge g i j -> Path g i j
edgeToPath a = [a]

public export
joinPath : Path g i j -> Path g j k -> Path g i k
joinPath [] y = y
joinPath (x :: xs) y = x :: joinPath xs y

public export
joinPathNil : (p : Path g i j) -> joinPath p [] = p
joinPathNil []        = Refl
joinPathNil (x :: xs) = cong (x ::) $ joinPathNil xs

public export
joinPathAssoc :
     (p : Path g i j)
  -> (q : Path g j k)
  -> (r : Path g k l)
  -> joinPath p (joinPath q r) = joinPath (joinPath p q) r
joinPathAssoc []        q r = Refl
joinPathAssoc (x :: xs) q r = cong (x ::) $ joinPathAssoc xs q r