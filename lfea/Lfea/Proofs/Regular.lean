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

-- It is accepted if the final state is part of the DFA final set
-- 
structure Dfa.Accepts (lang: List σ) (dfa: Dfa σ n) where
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

example : Dfa.Accepts [Alpha.a, Alpha.b] { state := 0, program := prog, final := {x | x = 2}} :=
    { proof := by simp [Dfa.extendedProgram, Set.in] }

-- NFA

-- Non deterministic returns a set
structure Nfa (sigma: Type) (n: Nat) where
  state    : Fin n -- Initial State
  program  : Fin n -> sigma -> Set (Fin n)
  final    : Set (Fin n) -- Final states

def Nfa.extendedProgram : Nfa σ n → Set (Fin n) → List σ → Set (Fin n)
  | nfa, qs, []        => qs
  | nfa, qs, (x :: xs) => 
    -- Its a confusing definition
    -- The result of the extended program is the 
    -- Big union of all the 
    Set.bigUnion { el | ∃q, q ∈ qs ∧ (el = extendedProgram nfa (nfa.program q x) xs) }

structure Nfa.Accepts (lang: List σ) (nfa: Nfa σ n) where
  proof : ∃q, q ∈ (Nfa.extendedProgram nfa {x | x = nfa.state} lang) ∧ q ∈ nfa.final

-- Denotational semantics of Regex

inductive Regex (σ: Type) where
  | var   : σ       -> Regex σ
  | alt   : Regex σ -> Regex σ -> Regex σ
  | conc  : Regex σ -> Regex σ -> Regex σ
  | star  : Regex σ -> Regex σ
  | empty : Regex σ


def sizeOfRegex : Regex σ -> Nat
  | Regex.var _     => 1
  | Regex.alt a b   => sizeOfRegex a + sizeOfRegex b
  | Regex.conc a b  => sizeOfRegex a + sizeOfRegex b
  | Regex.star _    => 1
  | Regex.empty     => 2

inductive Regex.Accepts : List σ → Regex σ → Type where
  | acceptsEmpty : Accepts [] Regex.empty
  | acceptsVar   : Accepts [x] (Regex.var x)
  | acceptsAltL  : Accepts x l → Accepts x (Regex.alt l r)
  | acceptsAltR  : Accepts x r → Accepts x (Regex.alt l r)
  | acceptsConc  : Accepts x a → Accepts y b → Accepts (x ++ y) (Regex.conc a b)
  | acceptsStar  : Accepts [] (Regex.star a)
  | acceptsStar2 : Accepts x a → Accepts y (Regex.star a) → Accepts (x ++ y) (Regex.star a)

theorem Regex.NotMatchesEmpty: ∀ {x : σ} {xs : List σ}, Regex.Accepts (x :: xs) Regex.empty → False
  | x, xs, accepts =>
    accepts.casesOn
      (motive := λacc regex proof => (acc = (x :: xs) -> regex = Regex.empty -> False))
      (λproof _ => List.noConfusion proof) -- acceptsEmpty
      (λproof ot => Regex.noConfusion ot) -- acceptsVar
      (λ_ _ ot => Regex.noConfusion ot) -- acceptsAltL
      (λ_ _ ot => Regex.noConfusion ot) -- acceptsAltR
      (λ_ _ _ ot => Regex.noConfusion ot) -- acceptsConc
      (λ _ ot => Regex.noConfusion ot) -- acceptsStar
      (λ_ _ _ ot => Regex.noConfusion ot) -- acceptsStar2
      rfl
      rfl

example : Regex.Accepts ['a', 'a', 'b'] (Regex.conc (Regex.star (Regex.var 'a')) (Regex.var 'b')) :=
  Regex.Accepts.acceptsConc
    (Regex.Accepts.acceptsStar2
      Regex.Accepts.acceptsVar
      (Regex.Accepts.acceptsStar2
        Regex.Accepts.acceptsVar
        Regex.Accepts.acceptsStar))
    Regex.Accepts.acceptsVar

-- iff redefined lol

structure IIff (a: Type u) (b: Type u) where
  to : a -> b
  mpr: b -> a

notation:40 a "`↔" b:40 => IIff a b

universe u

axiom IIff.toEql : ∀ {a b: Type u} (_: IIff a b), a = b

-- ENFA

def Nfa.Nfa_ε.End: Set (Fin 2) := { x | x = 1 }



def Nfa.Nfa_ε.Final: Fin 2 → Prop := { x | x = 0 }

def Nfa.Nfa_ε : Nfa σ 2 := { state := 0, program := λ _ _ => Nfa.Nfa_ε.End, final := { x | x = 0 }}

def Nfa.Nfa_ε.initial: ∀ {σ: Type}, Set (Fin 2) | x => {y | y = (@Nfa.state x 2 Nfa.Nfa_ε)}

theorem Nfa.Nfa_ε.EverythingLeadToEnd : ∀ {q: (Fin 2)} {x: σ}, (Nfa.Nfa_ε.program q x) = Nfa.Nfa_ε.End := by simp; rfl

theorem Nfa.Nfa_ε.EverythingToFinal : ∀ {xs: List σ}, (Nfa.extendedProgram Nfa.Nfa_ε Nfa.Nfa_ε.End xs) = Nfa.Nfa_ε.End
  | [] => by simp [Nfa.extendedProgram]
  | (x :: xs) => by
    simp [Nfa.extendedProgram, Set.bigUnion, Set.subset, Set.in]
    apply Set.Eq
    . intro x1
      simp [Set.in]
      intro ex
      apply Exists.elim
      . assumption
      . intro state proof
        simp [Set.in]
        apply Exists.elim
        . exact (And.right proof)
        . intro ata
          rw [Nfa.Nfa_ε.EverythingLeadToEnd, EverythingToFinal]
          intro wot
          rw [←wot.right]
          exact proof.left
    . simp [Nfa.extendedProgram, Set.bigUnion, Set.subset, Set.in]
      intro x1 end_x1
      exists End
      apply And.intro
      . assumption
      . exact ⟨1, by
          simp [End]
          rw [Nfa.Nfa_ε.EverythingLeadToEnd, EverythingToFinal]
          rfl⟩

theorem Nfa.Nfa_ε.LeadToFinal: ∀ {σ: Type} {x : σ} {xs: List σ}, (Nfa.extendedProgram Nfa.Nfa_ε (@Nfa.Nfa_ε.initial σ) (x :: xs)) = Nfa.Nfa_ε.End
  | sigm, x, xs => by
    simp [extendedProgram, Nfa.Nfa_ε.EverythingToFinal, Set.bigUnion, Set.in]
    apply Set.Eq
    . simp [Set.in, Set.subset]
      intro x ex
      apply Exists.elim
      . assumption
      . intro a p
        apply Exists.elim
        . exact p.right
        . intro b
          rw [Nfa.Nfa_ε.EverythingLeadToEnd, EverythingToFinal]
          intro f
          rw [←f.right]
          exact p.left
    . simp [Nfa.extendedProgram, Set.bigUnion, Set.subset, Set.in]
      intro x1 end_x1
      exists End
      apply And.intro
      . assumption
      . exact ⟨0, And.intro rfl (by rw [Nfa.Nfa_ε.EverythingLeadToEnd, Nfa.Nfa_ε.EverythingToFinal])⟩

theorem Nfa.Nfa_ε.NotAcceptsEntries: ∀ {σ: Type} {x : σ} {xs: List σ}, Nfa.Accepts (x :: xs) Nfa.Nfa_ε → False
  | sig, x, xs, p => absurd p.proof $ by
    let f : fun y => y = (@Nfa.state sig 2 Nfa.Nfa_ε) = (@Nfa.Nfa_ε.initial sig) := rfl
    simp [Set.in,  Nfa.Nfa_ε.LeadToFinal]
    intro x2
    apply Exists.elim
    . assumption
    . intro a
      rw [f, Nfa.Nfa_ε.LeadToFinal]
      simp [End, Nfa_ε]
      intro and
      let f := Eq.trans (Eq.symm and.left) and.right
      contradiction

def toNFA : ∀ (s: List σ), (r: Regex σ) → ∃ (n : Nat), ∃ (e: Nfa σ n), (Regex.Accepts s r) = (Nfa.Accepts s e)
  | s, Regex.empty =>
    let iffRes : (s: List σ) → (Regex.Accepts s Regex.empty) `↔ (Nfa.Accepts s Nfa.Nfa_ε)
      | [] => {
          to  := by
            intro a
            simp [Nfa.Nfa_ε, Nfa.Accepts]
            exact { proof := by simp [Nfa.extendedProgram]; exact ⟨0, rfl⟩ }
          mpr := λ _ => Regex.Accepts.acceptsEmpty
        }
      | (x :: xs) => {
        to := λ x => False.elim (Regex.NotMatchesEmpty x)
        mpr := λx => False.elim (Nfa.Nfa_ε.NotAcceptsEntries x)
      }
    ⟨2, ⟨Nfa.Nfa_ε, IIff.toEql (iffRes s)⟩⟩
  | s, Regex.var a     => sorry
  | s, Regex.star a    => sorry
  | s, Regex.conc a b  => sorry
  | s, Regex.alt a b   => sorry

-- Pumping lemma
-- Assume q₀ as the initial state and qf the final state, then
