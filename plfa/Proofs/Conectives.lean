import Proofs.Isomorphism

universe u 

-- And 

structure Pair (a b : Type u) where
  proj₁ : a 
  proj₂ : b

infixl:65   " ×´ " => Pair
notation:max "⟨" e "," f "⟩´" => Pair.mk e f

example : Int ×´ Int := ⟨2, 3⟩´

theorem Pair.comm : (a ×´ b) ≅ (b ×´ a) := 
  { To   := λ⟨a, b⟩´ => ⟨b, a⟩´
  , From := λ⟨b, a⟩´ => ⟨a, b⟩´
  , FromTo := λx => rfl 
  , ToFrom := λx => rfl }

theorem Pair.eta : ∀ {m n : Type}, (v : m ×´ n) → ⟨Pair.proj₁ v, Pair.proj₂ v⟩´ = v 
  | _, _, _ => rfl

-- Bottom and Top types

inductive T : Type 
  | t : T 

inductive F : Type 

notation:65 "⊤" => T
notation:65 "⊥" => F

notation:66 "¬" e "´" => (e → F)

theorem T.idₗ : ∀ {a : Type}, (⊤ ×´ a) ≅ a 
  := { To     := λ⟨a, b⟩´ => b
     , From   := λb       => ⟨T.t, b⟩´ 
     , FromTo := λx => rfl
     , ToFrom := λx => rfl  }

theorem F.elim (h : ⊥) : a := F.rec (fun _ => a) h

theorem Not.elim (e : a) (h : ¬a´) : ⊥ := h e

def Imp.contraposition : ∀ {a b : Type}, (a → b) → (¬b´ → ¬a´)
  | _, _, f, nb, na => nb (f na)  


notation:60 a "≢" b => ¬(a = b)

example : 2 ≢ 3 := λx => nomatch x

-- Or

inductive Prod' (a: Type) (b: Type) : Type 
  | inj₁ : a → Prod' a b
  | inj₂ : b → Prod' a b

infixl:65 " ⊎ " => Prod'

def Prod'.case : ∀ {a b c : Type}, (a → c) → (b → c) → a ⊎ b → c 
  | _, _, _, h1, h2, Prod'.inj₁ a => h1 a
  | _, _, _, h1, h2, Prod'.inj₂ b => h2 b

theorem Prod'.comm : ∀ {a b : Type}, a ⊎ b ≅ b ⊎ a 
  | a, b => { To     := Prod'.case Prod'.inj₂ Prod'.inj₁,   
              From   := Prod'.case Prod'.inj₂ Prod'.inj₁
              FromTo := fun | Prod'.inj₁ a => rfl
                            | Prod'.inj₂ b => rfl,
              ToFrom := fun | Prod'.inj₁ a => rfl
                            | Prod'.inj₂ b => rfl,
            }
    
