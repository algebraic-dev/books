import Lfea.Proofs.Set

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

structure Dfa (sigma: Type) (n: Nat) where
  state   : Fin n -- Initial State
  program : Fin n -> sigma -> Fin n -- Generating program
  final   : Set (Fin n) -- Final states

def Dfa.extendedProgram : Dfa σ n → Fin n → List σ → Fin n
  | dfa, q, []        => q
  | dfa, q, (x :: xs) => extendedProgram dfa (dfa.program q x) xs

structure IsAccepted (lang: List σ) (dfa: Dfa σ n) where
  proof : (Dfa.extendedProgram dfa dfa.state lang) ∈ dfa.final

inductive Alpha where
  | a
  | b

def prog : Fin 4 -> Alpha -> Fin 4
  | 0, Alpha.a => 1
  | 1, Alpha.b => 2
  | 1, Alpha.a => 1
  | 2, Alpha.a => 2
  | _, _ => 3

example : IsAccepted [Alpha.a, Alpha.b] { state := 0, program := prog, final := {x | x == 2}} :=
    { proof := by simp [Dfa.extendedProgram, Set.in] }

-- NFA

-- Non deterministic returns a set
structure Nfa (sigma: Type) (n: Nat) where
  state    : Fin n -- Initial State
  program  : Fin n -> sigma -> Set (Fin n)
  final    : Set (Fin n) -- Final states

def Nfa.extendedProgram : Nfa σ n → Set (Fin n) → List σ → Set (Fin n)
  | nfa, qs, []        => qs
  | nfa, qs, (x :: xs) => Set.bigUnion
    { el | ∃q, q ∈ qs ∧ (el = extendedProgram nfa (nfa.program q x) xs) }

-- Denotational semantics of Regex

inductive Regex (σ: Type) where
  | var   : σ       -> Regex σ
  | alt   : Regex σ -> Regex σ -> Regex σ
  | conc  : Regex σ -> Regex σ -> Regex σ
  | plus  : Regex σ -> Regex σ
  | empty : Regex σ
