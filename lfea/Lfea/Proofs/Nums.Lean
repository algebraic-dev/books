inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ

def ℕ.add : ℕ → ℕ → ℕ
  | ℕ.zero,   m => m
  | ℕ.succ n, m => ℕ.succ (add n m)

-- succ m * 0 = 0 : Prop
-- 0 + (m * 0)
-- (m * 0) = 0
def ℕ.mul : ℕ → ℕ → ℕ
  | ℕ.zero,          m => ℕ.zero
  | ℕ.succ n,        m => add m (mul n m)

def fromDefaultNat : Nat → ℕ
  | 0   => ℕ.zero
  | n+1 => ℕ.succ (fromDefaultNat n)

def toDefaultNat : ℕ → Nat
  | ℕ.zero   => 0
  | ℕ.succ n => Nat.succ (toDefaultNat n)

instance : OfNat ℕ n where ofNat := fromDefaultNat n
instance : Repr ℕ where reprPrec x _ := repr (toDefaultNat x)

instance : HAdd ℕ ℕ ℕ where hAdd := ℕ.add
instance : HMul ℕ ℕ ℕ where hMul := ℕ.mul

theorem ℕ.Add.Succ.shiftR : ∀ { n m : ℕ }, n + ℕ.succ m = ℕ.succ (n + m)
  | ℕ.zero   => rfl
  | ℕ.succ n => congrArg ℕ.succ shiftR

theorem ℕ.Add.neutralL : ∀ { n : ℕ }, n + ℕ.zero = n
  | ℕ.zero   => rfl
  | ℕ.succ m => congrArg ℕ.succ neutralL

theorem ℕ.Add.comm : ∀ { m n : ℕ }, m + n = n + m
  | ℕ.zero,   m => by rw [ℕ.Add.neutralL]; rfl
  | ℕ.succ n, m => by rw [ℕ.Add.Succ.shiftR]; exact (congrArg ℕ.succ comm)

theorem ℕ.Add.assoc : ∀ { m n k : ℕ }, (m + n) + k = m + (n + k)
  | ℕ.zero,   n, k => rfl
  | ℕ.succ m, n, k => congrArg ℕ.succ assoc

theorem ℕ.Mul.neutralL : ∀ { n : ℕ }, n * 1 = n
  | ℕ.zero        => rfl
  | ℕ.succ m      => congrArg ℕ.succ (@neutralL m)

theorem ℕ.Mul.absL : ∀ { n : ℕ }, n * ℕ.zero = ℕ.zero
  | ℕ.zero        => rfl
  | ℕ.succ m      => by simp [ℕ.mul]; exact (@absL m)

theorem ℕ.Mul.succL : ∀ { m n : ℕ }, succ m * n = n + (m * n) := rfl
theorem ℕ.Add.redc : ∀ { m n : ℕ }, succ m + n = succ (m + n) := rfl

theorem ℕ.Mul.succR : ∀ { m n : ℕ }, m * succ n = m + (m * n)
  | ℕ.zero, n    => rfl
  | ℕ.succ m, n  => by -- It's just a test lol i now it's bad
    rw [ℕ.Mul.succL]
    simp [ℕ.Add.redc]
    rw [succR]
    rw [ℕ.Mul.succL]
    rw [←ℕ.Add.assoc]
    rw [@ℕ.Add.comm n m]
    rw [ℕ.Add.assoc]

theorem ℕ.Mul.comm : ∀ { m n : ℕ }, m * n = n * m
  | ℕ.zero,   n => by rw [ℕ.Mul.absL]; rfl
  | ℕ.succ m, n => by rw [succL, succR, comm]
