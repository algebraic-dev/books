import Proofs.Naturals

inductive le : ℕ → ℕ → Type where 
  | zLEN : {n : ℕ} → le 0 n 
  | sLEN : le m n  → le (ℕ.s m) (ℕ.s n) 

macro_rules | `($x ≤ $y)  => `(le $x $y)

example : (2 ≤ 4) := le.sLEN (le.sLEN (le.zLEN))

theorem invLE : ℕ.s m ≤ ℕ.s n → m ≤ n | le.sLEN n => n
theorem invZE : ∀{m : ℕ}, m ≤ 0 → m = 0 | _, le.zLEN => rfl

-- Relation types
-- Reflexive: a ≤ n holds
-- Transitive: if m ≤ n and n ≤ j then m ≤ j
-- Antisimetric: if m ≤ n and n ≤ m then m = n
-- Total: forall a b either a ≤ b or b ≤ a holds

-- Pre order: reflexive + transative
-- Partial order: also antisimetric
-- Total oroder: also total

inductive Total : ℕ → ℕ → Type where 
  | forward : m ≤ n → Total m n 
  | flipped : n ≤ m → Total m n 

def totalSuc : Total m n → Total (ℕ.s m) (ℕ.s n)
  | Total.forward m => Total.forward (le.sLEN m)
  | Total.flipped m => Total.flipped (le.sLEN m)

theorem Le.refl : ∀ {m : ℕ}, m ≤ m   
  | 0 => le.zLEN
  | ℕ.s m => le.sLEN (@refl m)

theorem Le.trans : m ≤ n → n ≤ p → m ≤ p
  | le.zLEN, n => le.zLEN
  | le.sLEN m, le.sLEN n => le.sLEN (trans m n)

theorem Le.antiSym : m ≤ n → n ≤ m → m = n 
  | le.zLEN, le.zLEN => rfl
  | le.sLEN m, le.sLEN n => congrArg ℕ.s (antiSym m n)

theorem Le.total : ∀ {m n : ℕ}, Total m n
  | 0, n => Total.forward le.zLEN
  | n, 0 => Total.flipped le.zLEN
  | ℕ.s m, ℕ.s n => totalSuc (@total m n)

theorem Le.Add.monoLeft: ∀ {m n p : ℕ}, m ≤ n → p + m ≤ p + n
  | m, n, 0, hip   => hip
  | m, n, ℕ.s p, hip => le.sLEN (@monoLeft m n p hip)

theorem Le.Add.monoRight {m n p : ℕ} : m ≤ n → m + p ≤ n + p := by 
  simp [Nt.Add.comm m p, Nt.Add.comm n p]
  apply Le.Add.monoLeft

theorem Le.Add.mono : ∀ {m n p q : ℕ}, (m ≤ n) → (p ≤ q) → (p + m ≤ q + n)
  | m, n, p, q, h1, h2 => Le.trans (@Le.Add.monoLeft m n p h1) (@Le.Add.monoRight p q n h2)

theorem Le.Mul.monoLeft : ∀ {m n p : ℕ}, (m ≤ n) → (p * m ≤ p * n)
  | m, n, 0, h1     => by simp [Nt.Mul.leftNeutral]; exact le.zLEN
  | m, n, ℕ.s p, h1 => by 
    simp [Nt.Mul.sucLeft]; 
    apply (Le.Add.mono (@monoLeft m n p h1) h1)

theorem Le.Mul.mono : ∀ {m n p q : ℕ}, (m ≤ n) -> (p ≤ q) → (p * m ≤ q * n)
  | m, n, 0    , q, h1, h2 => by simp [Nt.Mul.leftNeutral]; exact le.zLEN
  | m, n, ℕ.s p, ℕ.s q, h1, h2 => by 
    simp [Nt.Mul.sucLeft]; 
    exact (@Le.Add.mono (p*m) (q*n) m n (@mono m n p q h1 (invLE h2)) h1)
    
-- Inequality 

inductive ls : ℕ → ℕ → Type where 
  | zLEN : {n : ℕ} → ls 0 (ℕ.s n) 
  | sLEN : ls m n  → ls (ℕ.s m) (ℕ.s n) 

macro_rules | `($x < $y)  => `(ls $x $y)

inductive Tricotomy : ℕ → ℕ → Type where 
  | lessT  : {n m : ℕ} → ls n m → Tricotomy n m
  | greatT : {n m : ℕ} → ls m n → Tricotomy n m
  | eqT    : {n : ℕ}           → Tricotomy n n

def succTricotomy : Tricotomy m n → Tricotomy (ℕ.s m) (ℕ.s n)
  | Tricotomy.eqT      => Tricotomy.eqT 
  | Tricotomy.lessT p  => Tricotomy.lessT (ls.sLEN p)
  | Tricotomy.greatT p => Tricotomy.greatT (ls.sLEN p)

theorem tricotomy : ∀ {m n}, Tricotomy m n
  | 0    , 0     => Tricotomy.eqT
  | ℕ.s m, 0     => Tricotomy.greatT ls.zLEN
  | 0    , ℕ.s n => Tricotomy.lessT ls.zLEN
  | ℕ.s m, ℕ.s n => succTricotomy (@tricotomy m n)

theorem Ls.trans : m < n → n < p → m < p 
  | ls.zLEN  , ls.sLEN m => ls.zLEN 
  | ls.sLEN m, ls.sLEN n => ls.sLEN (trans m n)

theorem Ls.Add.monoLeft : ∀ {m n p: ℕ}, m < n → (p + m < p + n)
  | m, n, 0, h1 => h1
  | m, n, ℕ.s p, h1 => ls.sLEN (@monoLeft m n p h1)

theorem Ls.Add.monoRight : ∀ {m n p: ℕ}, m < n → (m + p < n + p)
  | m, n, 0, h1 => by simp [Nt.Add.rightId]; exact h1
  | m, n, ℕ.s p, h1 => by rw [Nt.Add.comm m (ℕ.s p), Nt.Add.comm n (ℕ.s p)]; exact (@Ls.Add.monoLeft m n (ℕ.s p) h1)

theorem Ls.Add.mono {m n p q : ℕ} (h1: m < n) (h2: p < q) : (p + m < q + n) := 
  Ls.trans (@Ls.Add.monoLeft m n p h1) (@Ls.Add.monoRight p q n h2)

theorem Ls.Eq.iff : ∀ {m n : ℕ}, ℕ.s m ≤ n → m < n 
  | ℕ.z, ℕ.s n, le.sLEN _ => ls.zLEN
  | ℕ.s m, ℕ.s n, le.sLEN o => ls.sLEN (iff o)

theorem Ls.Eq.iffInv : ∀ {m n : ℕ}, m < n → ℕ.s m ≤ n 
  | 0,     ℕ.s n, ls.zLEN   => le.sLEN le.zLEN
  | ℕ.s m, ℕ.s n, ls.sLEN o => le.sLEN (iffInv o)

theorem Ls.toLs : ∀ {m n : ℕ}, m < n → m ≤ n 
  | 0,     ℕ.s n, ls.zLEN   => le.zLEN
  | ℕ.s m, ℕ.s n, ls.sLEN o => le.sLEN (toLs o)

theorem leTransRevisited (h1: m < n) (h2: n < p): m < p := Ls.Eq.iff (Le.trans (Ls.Eq.iffInv h1) (Ls.toLs h2))