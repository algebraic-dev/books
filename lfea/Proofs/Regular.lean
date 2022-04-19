-- An alphabet is a finite set of symbols or letters
-- A word is a finite sequence of letters with only one symbol
-- being valid that is the ε that means empty

-- A word over an alphabet α is a list of α? probably.

-- A formal language over an alpha bet A is a: L ⊆ A*
-- (The reflexive and transitive closure under A)

-- Chomsky grammar is a 4-tuple G = (V, T, P, S)
-- Where
-- - V = Finite set of variable symbols or non terminals
-- - T = Finite set of symbols disjoint of V
-- - P = (V ∪ T)+ -> (V ∪ T)* finite relations of production rules
-- - S = distinguished from V (initial symbol)

-- Derivation rule ⟹
-- The transitive closure of the derivation rule makes it derive
-- one or more symbols at once

-- Generated language is the language that is derived from the language
-- that we can achieve using Derivation rule from the start symbol

-- Finite automatas are operational semantics
-- Regular expressions are denotational semantics
-- Regular grammar are axiomatic semantics

-- Σ alphabet of input symbols
-- Q possible states
-- δ program (transition function)

-- δ: Q × Σ → Q
