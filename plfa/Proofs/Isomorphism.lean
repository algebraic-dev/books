import Proofs.Naturals

universe u 

-- If two functions returns the same things for the same inputs then they're equal!
axiom extensionality : ∀ { a b : Type u } { f g : a → b }, (∀ (x : a), f x = g x) → (f = g)

theorem sameAddComm : ∀ (m n : ℕ), (add n m) = (add' m n)
  | m, 0 => by simp [add, add']; 
  | m, ℕ.s n => by simp [add, add']; exact (sameAddComm m n)

theorem sameAdd (m n : ℕ) : (add n m) = (add' n m) := by rw [Nt.Add.comm n m]; apply sameAddComm

theorem sameFunAdd : add = add' := extensionality (λm => extensionality (λn => sameAdd n m))

structure Iso (A B : Type) where 
  To : A → B 
  From : B → A
  FromTo : ∀ (x : A), (From (To x) = x)
  ToFrom : ∀ (y : B), (To (From y) = y)

infixl:60 "≅" => Iso

theorem Iso.refl : ∀ {a : Type}, a ≅ a 
  | a => { To := λx => x, From := λy => y, FromTo := λx => rfl, ToFrom := λx => rfl }

theorem Iso.sym : ∀ {A B : Type}, A ≅ B → B ≅ A
  | x, y, t => { To := t.From, 
                 From := t.To, 
                 FromTo := Iso.ToFrom t, 
                 ToFrom := Iso.FromTo t
               }

theorem Iso.trans : ∀ { a b c : Type }, a ≅ b → b ≅ c → a ≅ c 
  | x, y, z, h1, h2 => 
    { To     := h2.To ∘ h1.To,
      From   := h1.From ∘ h2.From,
      FromTo := by simp[Iso.FromTo h2, Iso.FromTo h1];
      ToFrom := by simp[Iso.ToFrom h2, Iso.ToFrom h1];
    }

-- Embedding is the notion that one function is included in other

structure Emb (A B : Type) where 
  To : A → B 
  From : B → A
  FromTo : ∀ (x : A), (From (To x) = x)

macro_rules | `($x emb< $y)  => `(Emb $x $y)

theorem Emb.refl : ∀ {a : Type}, a emb< a 
  | a => { To := λx => x, From := λy => y, FromTo := λx => rfl }

theorem Emb.trans : ∀ { a b c : Type }, a emb< b → b emb< c → a emb< c 
  | x, y, z, h1, h2 => 
    { To     := h2.To ∘ h1.To,
      From   := h1.From ∘ h2.From,
      FromTo := by simp[Emb.FromTo h2, Emb.FromTo h1];
    }