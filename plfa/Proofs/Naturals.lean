-- Mathematical induction is the process of, by simple rules,
-- we achieve a generalization (the opposite of deduction).
-- Inductive data types follows the same principles, they
-- have a base case and a inductive case.

inductive ℕ : Type where 
  | z : ℕ      -- Here "z" (zero) is the base case
  | s : ℕ → ℕ  -- And "s" (sucessor) is the inductive case

theorem seven : ℕ := ℕ.s (ℕ.s (ℕ.s (ℕ.s (ℕ.s (ℕ.s (ℕ.s ℕ.z)))))) 

-- Some cool definitions to make it easier to work with this new
-- data type

def fromDefaultNat : Nat → ℕ
  | 0   => ℕ.z
  | n+1 => ℕ.s (fromDefaultNat n)

def toDefaultNat : ℕ → Nat 
  | ℕ.z   => 0
  | ℕ.s n => Nat.succ (toDefaultNat n)

instance : OfNat ℕ n where ofNat := fromDefaultNat n
instance : Repr ℕ where reprPrec x _ := repr (toDefaultNat x)

-- Operations are defined recursively like that

def add : ℕ → ℕ → ℕ 
  | ℕ.z,   m => m 
  | ℕ.s n, m => ℕ.s (add n m)

def add' : ℕ → ℕ → ℕ 
  | m, ℕ.z   => m 
  | m, ℕ.s n => ℕ.s (add' m n)

def mult : ℕ → ℕ → ℕ 
  | ℕ.z,   m    => ℕ.z
  | ℕ.s ℕ.z,  m => m 
  | ℕ.s n, m    => add m (mult n m)

-- Like subtraction but trim at zero

def monus : ℕ → ℕ → ℕ
  | ℕ.z,       m => ℕ.z 
  | m,       ℕ.z => m
  | ℕ.s m, ℕ.s n => monus m n

infixl:65   " + " => add
infixl:66   " * " => mult

instance : HSub ℕ ℕ ℕ where hSub := monus

example : 3 * 3 + 5 - 4 = 10 := rfl

-- Binary natural numbers

inductive 𝔹 : Type where 
  | nob  : 𝔹
  | zero : 𝔹 → 𝔹
  | one  : 𝔹 → 𝔹
  deriving Repr

def Bin.inc : 𝔹 → 𝔹
  | 𝔹.nob    => 𝔹.one 𝔹.nob
  | 𝔹.zero n => 𝔹.one n
  | 𝔹.one  n => 𝔹.zero (inc n)

def Bin.toNat : 𝔹 → ℕ 
  | 𝔹.nob    => ℕ.z
  | 𝔹.zero n => toNat n * 2
  | 𝔹.one  n => toNat n * 2 + 1

def Nat.toBin : ℕ → 𝔹
  | ℕ.z   => 𝔹.nob 
  | ℕ.s n => Bin.inc (toBin n)

instance : OfNat 𝔹 n where ofNat := Nat.toBin (fromDefaultNat n)

-- Proofs

theorem Nt.Add.sucAssoc : ∀ (m n : ℕ), ℕ.s m + n = ℕ.s (m + n)
  | ℕ.z, n   => rfl
  | ℕ.s m, n => congrArg ℕ.s (sucAssoc m n)

theorem Nt.Add.sucShift : ∀ (m n : ℕ), ℕ.s m + n = m + ℕ.s n
  | ℕ.z, n => rfl
  | ℕ.s m, n => Eq.trans (Nt.Add.sucAssoc (ℕ.s m) n) (congrArg ℕ.s (sucShift m n))

theorem Nt.Add.assoc : ∀ (m n p : ℕ), (m + n) + p = m + (n + p)
  | ℕ.z  , n, p => rfl
  | ℕ.s m, n, p => by 
    rw    [Nt.Add.sucAssoc]
    apply congrArg ℕ.s (assoc m n p)

theorem Nt.Add.rightId : ∀ (m : ℕ), m + 0 = m
  | ℕ.z   => rfl 
  | ℕ.s n => congrArg ℕ.s (rightId n)

theorem Nt.Add.comm : ∀ (m n : ℕ), m + n = n + m
  | 0,   n => Eq.symm (Nt.Add.rightId n)
  | ℕ.s m, n => by 
    rw [Nt.Add.sucAssoc m n, comm m n, ← Nt.Add.sucShift n m]
    rfl
    
theorem Nt.Mul.leftId : ∀ (m : ℕ), ℕ.s 0 * m = m 
  | 0 => rfl
  | ℕ.s m => rfl 
  
theorem Nt.Mul.leftNeutral : ∀ (m : ℕ), 0 * m = 0
  | 0     => rfl
  | ℕ.s m => rfl

theorem Nt.Mul.sucLeft : ∀ (m n : ℕ), ℕ.s m * n = n + (m * n)
  | 0, n     => by apply (Eq.symm (Nt.Add.rightId n))
  | ℕ.s m, n => by rfl 

theorem Nt.Mul.sucRight : ∀ (m n : ℕ), m * ℕ.s n = (m * n) + m
  | 0, n     => by simp; rfl
  | ℕ.s m, n => by rw [Nt.Mul.sucLeft m, Nt.Mul.sucLeft, sucRight m n, Nt.Add.assoc, Nt.Add.sucShift, ←Nt.Add.sucAssoc, Nt.Add.sucShift];

theorem Nt.Mul.distribAdd : ∀ (m n p : ℕ), (m + n) * p = m * p + n * p
  | 0  , n, p   => by rfl
  | ℕ.s m, n, p => by 
    rw [Nt.Add.sucAssoc]
    simp [Nt.Mul.sucLeft]
    rw [distribAdd m n p, Nt.Add.assoc]

theorem Nt.Mul.rightNeutral : ∀ (m : ℕ), m * 0 = 0
  | 0     => rfl
  | ℕ.s m => by rw[Nt.Mul.sucLeft, rightNeutral m]; rfl

theorem Nt.Mul.rightId : ∀ (m : ℕ), m * ℕ.s 0 = m
  | 0     => rfl
  | ℕ.s m => by rw[Nt.Mul.sucLeft, rightId m]; rfl

theorem Nt.Mul.comm :  ∀ (m n : ℕ), m * n = n * m
  | 0  ,   n => Eq.symm (Nt.Mul.rightNeutral n) 
  | ℕ.s m, n => by rw [Nt.Mul.sucRight, Nt.Mul.sucLeft, Nt.Add.comm, comm]

-- Binary 

theorem Bin.incEqNatSuc : ∀ (b : 𝔹), Bin.toNat (Bin.inc b) = ℕ.s (Bin.toNat b)
  | 𝔹.nob => rfl
  | 𝔹.zero n => by simp [Bin.toNat]; rw [Nt.Add.comm]; rfl
  | 𝔹.one n => by 
    simp [Bin.toNat]
    rw [Nt.Add.comm, incEqNatSuc, Nt.Mul.sucLeft]
    rfl

theorem Bin.eqNat : ∀ (n : ℕ), Bin.toNat (Nat.toBin n) = n 
  | 0     => rfl
  | ℕ.s n => by simp [Nat.toBin]; rw [Bin.incEqNatSuc, eqNat]; 

