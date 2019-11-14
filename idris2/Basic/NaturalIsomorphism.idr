module Basic.NaturalIsomorphism

import Basic.Category
import Basic.Functor
import Basic.Isomorphism
import Cats.FunctorsAsCategory

public export
NaturalIsomorphism: {cat1, cat2: Category} -> (fun1 : CFunctor cat1 cat2) -> (fun2 : CFunctor cat1 cat2) -> Type
NaturalIsomorphism {cat1} {cat2} fun1 fun2 = Isomorphism (functorCategory cat1 cat2) fun1 fun2
