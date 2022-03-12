-- Leibniz equality: two objects are equal if they satisfy the 
-- same properties

universe u

def leibnizEq : ∀ { a : Type u }, (x y : a) → Type (u + 1) 
  | a, x, y => ∀ {P : a → Type u}, P x → P y

macro_rules | `($x ·= $y)  => `(leibnizEq $x $y)

theorem LeiEq.refl : ∀ {x : Type u }, x ·= x := λx => x

theorem LeiEq.trans : ∀ { x y z : Type u }, x ·= y → y ·= z → x ·= z 
  | _, _, _, h1, h2 => λx => h2 (h1 x)