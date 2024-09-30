import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

structure Constructor where
  name : String
  arity : ℕ
  deriving DecidableEq

inductive Value where
| Constructor : Constructor → List Value → Value

inductive Pattern where
| Wildcard : Pattern
| Constructor : Constructor → List Pattern → Pattern
| Or: Pattern → Pattern → Pattern



def instanceOf (p : Pattern) (v : Value) : Bool :=
  match p with
  | .Wildcard => true
  | .Or p1 p2 => instanceOf p1 v || instanceOf p2 v
  | .Constructor c ps =>
    match v with
    | .Constructor n vs =>
      match decEq c n with
      | isFalse _ => false
      | isTrue _ =>
        match ps, vs with
        | [], [] => true
        | [], _ => false
        | _, [] => false
        | .cons p' ps', .cons v' vs' =>
          instanceOf p' v' && instanceOf (Pattern.Constructor c ps') (Value.Constructor n vs')


abbrev Action := Nat

-- abbrev ClauseMatrix m n := Matrix (Fin m) (Fin n) Pattern × Matrix (Fin m) Unit Action

-- def MLmatch (v : Matrix Unit (Fin n) Value)
--             (P : Matrix (Fin m) (Fin n) Pattern)
--             (A : Matrix (Fin m) Unit Action) : Action :=
--   sorry


-- Matrix decomposition

-- def lineSpecialization
--       (c : Constructor)
--       (P : Matrix Unit (Fin n) Pattern)
--       (A : Action)
--       : Matrix Unit (Fin (c.arity + n - 1)) Pattern :=
--         match P Unit.unit (Fin.ofNat 0) with
--         | .Wildcard => sorry
--         | .Constructor c' ps => sorry
--         | .Or p1 p2 => sorry

-- def specialization
--       (c : Constructor)
--       (P : Matrix (Fin m) (Fin n) Pattern)
--       (A : Matrix (Fin m) Unit Action)
--       : Σ m' : ℕ, Matrix (Fin m') (Fin (c.arity + n - 1)) Pattern :=

--         sorry


def lineSpecialization {n : ℕ}
      (c : Constructor)
      (P : Matrix Unit ℕ Pattern)
      (A : Action)
      : Matrix Unit ℕ Pattern :=
        match P Unit.unit 0 with
        | .Wildcard => sorry
        | .Constructor c' ps => sorry
        | .Or p1 p2 => sorry

def specialization
      (c : Constructor)
      (P : Matrix m n Pattern)
      (A : Matrix m Unit Action)
      : Σ m' : ℕ, Matrix ℕ ℕ Pattern :=

        sorry
