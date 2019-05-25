module CategoryReasoning

import Basic.Category

%access public export
%default total

-- Preorder reasoning syntax for morphisms in a category
||| Used for preorder reasoning syntax. Not intended for direct use.
qed : (cat : Category) -> (a : obj cat) -> mor _ a a
qed cat a = identity cat a

||| Used for preorder reasoning syntax. Not intended for direct use.
step : (cat : Category) -> (a : obj cat) -> mor cat a b -> mor cat b c -> mor cat a c
step cat a f g = compose _ _ _ _ f g

liftEquality : (cat : Category) -> (a, b : obj cat) -> a = b -> mor cat a b
liftEquality cat a a Refl = identity _ a
