
def Ident : Type := String deriving BEq

inductive Term where
  | var : Ident → Term
  | abs : Ident → Term → Term
  | app : Term  → Term → Term

  | zero : Term
  | succ : Term → Term

  | case : Term → Term → Ident → Term → Term
  | fixpoint : Ident → Term → Term

open Term

notation:64 "μ" x "=>" v => Term.fixpoint x v
notation:65 "⬝λ" x "=>" v => Term.abs x v
notation:66 "⬝case" cond "of" "|" "z" "=>" a "|" "s" b "=>" c => Term.case cond a b c
prefix:100 "⬝" => Term.var
infixl:67   "▸" => Term.app

inductive Value : Term → Type where
  | vAbs  : ∀ {x} {N}, Value (⬝λx => N)
  | vZero : Value zero
  | vSucc : ∀ {v}, Value v → Value (succ v)

-- Some examples

def plus : Term :=
  let m := var "m"
  let n := var "n"
  let plus := var "plus"
  μ "+" => ⬝λ "m" => ⬝λ "n" =>
    ⬝case (⬝"m") of
      | z     => n
      | s "m" => succ ((plus ▸ m) ▸ n)

def mult : Term :=
  let m := var "m"
  let n := var "n"
  let plus := var "plus"
  let mult := var "mult"
  μ "*" => ⬝λ "m" => ⬝λ "n" =>
    ⬝case m of
      | z     => zero
      | s "m" =>
          ⬝case m of
            | z     => n
            | s "_" => (plus ▸ n) ▸ ((mult ▸ m) ▸ n)


-- Substitution

mutual
  def boundSubs (from_ : Ident) (to: Term) (app: Ident → Term → Term) (binder: Ident) (body: Term) : Term :=
    if binder == from_
      then app binder body
      else app binder (substitute from_ to body)

  def substitute (from_ : Ident) (to : Term) : Term → Term
    | var x   => if x == from_ then to else var x
    | app a b => app (substitute from_ to a) (substitute from_ to b)
    | zero    => zero
    | succ e  => succ (substitute from_ to e)
    | abs param body => boundSubs from_ to abs param body
    | fixpoint n t   => boundSubs from_ to fixpoint n t
    | case cond onZ name onS =>
      boundSubs from_ to (case (substitute from_ to cond) (substitute from_ to onZ)) name onS
end

termination_by
  boundSubs f     => (sizeOf f, 1)
  substitute expr => (sizeOf expr, 0)

notation:72 x "[" from_ ":=" to_ "]" => substitute from_ to_ x

-- β-Reduction as a fucking hellish data

inductive BetaReduction : Term → Term → Type where
  | xiApp1   : BetaReduction L L' → BetaReduction (L ▸ M) (L' ▸ M)
  | xiApp2   : BetaReduction L L' → BetaReduction (M ▸ L) (M ▸ L')
  | betaLam  : Value V → BetaReduction (⬝λ "n" => N) (N["n" := V])
  | xiSuc    : BetaReduction M N → BetaReduction (succ m) (succ n)
  | xiCase   : BetaReduction L L' → BetaReduction (⬝case L of | z => M | s X => N)
                                                  (⬝case L' of | z => M | s X => N)
  | betaZero : Value V → BetaReduction (⬝case zero of     | z => M | s X => N) N
  | betaSuc  : Value V → BetaReduction (⬝case (succ V) of | z => M | s X => N) (M[X := V])
  | betaFix  : BetaReduction (μ X => M) (M[X := (μ X => M)])

infixl:67 "-β→" => BetaReduction


