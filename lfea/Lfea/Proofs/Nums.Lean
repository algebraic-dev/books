inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ

def ℕ.add : ℕ → ℕ → ℕ
  | ℕ.zero,   m => m
  | ℕ.succ n, m => ℕ.succ (add n m)

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

def ℕ.divider : ℕ → ℕ → ℕ → ℕ → ℕ
  | c, d, ℕ.zero,      j          => c
  | c, d, (ℕ.succ i),  ℕ.zero     => divider (ℕ.succ c) d i d
  | c, d, (ℕ.succ i),  (ℕ.succ j) => divider c          d i j

def ℕ.divide : ℕ → ℕ → ℕ
  | n, ℕ.succ d => ℕ.divider 0 d n d
  | n, ℕ.zero   => ℕ.zero

inductive ℕz where
  | one : ℕz
  | succ : ℕz → ℕz

def ℕz.toDefaultNat : ℕz → Nat
  | ℕz.one    => 1
  | ℕz.succ n => Nat.succ (toDefaultNat n)

def ℕz.pred : ℕz → ℕz
  | ℕz.one    => ℕz.one
  | ℕz.succ m => m

def ℕz.toNat : ℕz -> ℕ
  | ℕz.one    => ℕ.succ ℕ.zero
  | ℕz.succ m => ℕ.succ (toNat m)

def ℕ.toNzAux : ℕ → ℕz
  | ℕ.zero   => ℕz.one
  | ℕ.succ m => ℕz.succ (toNzAux m)

def ℕ.toNz : ℕ → ℕz := λx => ℕz.pred (ℕ.toNzAux x)

instance : Repr ℕz where reprPrec x _ := repr (ℕz.toDefaultNat x)
instance : OfNat ℕz n where ofNat := ℕ.toNz (fromDefaultNat n)

instance : OfNat ℕ n where ofNat := fromDefaultNat n
instance : Repr ℕ where reprPrec x _ := repr (toDefaultNat x)

inductive ℤ where
  | pos : ℕ  → ℤ
  | neg : ℕz → ℤ

instance : Repr ℤ where reprPrec
  | ℤ.pos x, _ => "+" ++ repr (toDefaultNat x)
  | ℤ.neg x, _ => "-" ++ repr (ℕz.toDefaultNat x)

def ℤ.divide : ℤ → ℤ → ℤ
  | ℤ.pos m, ℤ.pos n => ℤ.pos (ℕ.divide m n)
  | ℤ.pos m, ℤ.neg n => ℤ.neg (ℕ.toNz (ℕ.divide m (ℕz.toNat n)))
  | ℤ.neg m, ℤ.pos n => ℤ.neg (ℕ.toNz (ℕ.divide (ℕz.toNat m) n))
  | ℤ.neg m, ℤ.neg n => ℤ.pos (ℕ.divide (ℕz.toNat m) (ℕz.toNat n))

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
