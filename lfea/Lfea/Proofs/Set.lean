def Set (α : Type u) : Type u := α → Prop

def Set.in (elem : α) (set : Set α): Prop := set elem

notation "{" a "|" b "}" => λa => b

notation:40 a "∈" b:40 => Set.in a b
notation:40 a "∉" b:40 => ¬ Set.in a b

def Set.subset (a: Set α) (b: Set α) : Prop := ∀x, x ∈ a → x ∈ b
def Set.union  (a: Set α) (b: Set α) : Set α := { x | x ∈ a ∨ x ∈ b}
def Set.inter  (a: Set α) (b: Set α) : Set α := { x | x ∈ a ∧ x ∈ b}
def Set.diff   (a: Set α) (b: Set α) : Set α := { x | x ∈ a ∧ x ∉ b}
def Set.compl  (a: Set α)            : Set α := { x | x ∉ a}

def Set.bigUnion (a: Set (Set α)) : Set α := { x | ∃(y: Set α), x ∈ y ∧ y ∈ a }

prefix:64 "⋃." => Set.bigUnion
infix:64 "⊆" => Set.subset
infix:65 "∪" => Set.union
infix:66 "∩" => Set.inter
infix:67 "–" => Set.diff
prefix:67 "⬝~" => Set.compl

def Set.power  (a: Set α)          : Set (Set α) := { x      | x ⊆ a }
def Set.prod (a: Set α) (b: Set β) : Set (α × β) := { (x, y) | x ∈ a ∧ y ∈ b}
def Set.fun  (a: Set α) (b: Set β) : Set (α × β) := { (x, y) | x ∈ a ∧ y ∈ b}

infix:67 "`×" => Set.prod

theorem Set.Compl.InterEq {a b: Set α} : a – b = a ∩ ⬝~b := by
  simp [Set.in, Set.diff, Set.inter, Set.compl]

@[simp]
def Set.Relation.Closure.Trans (r: Set (α × α)) : Set (α × α) :=
  { (x, y) | (x,y) ∈ r ∨ (∃z, (x, z) ∈ r ∧ (z, y) ∈ r) }

@[simp]
def Set.Relation.Closure.ReflTrans (r: Set (α × α)) : Set (α × α) :=
  { (x, y) | (x,y) ∈ r ∨ (∃z, (x, z) ∈ r ∧ (z, y) ∈ r) }

@[simp]
def setEx : Set (Int × Int) :=
  { (x, y) | (x,y) = (1,2) ∨ (x,y) = (2,3) ∨ (x,y) = (3,4) ∨ (x,y) = (1,5) }

example : ((1, 3) ∈ (Set.Relation.Closure.Trans setEx)) := by
  simp [Set.in]
  apply ⟨2, And.intro (Or.inl rfl) rfl⟩

example : 3 ∈ Set.bigUnion {x | x = {y | y == 1 ∨ y == 2} ∨  x = {y | y == 3 ∨ y == 4 } } := by 
  simp [Set.bigUnion, Set.in]
  exists {y | y == 3 ∨ y == 4 }
  simp