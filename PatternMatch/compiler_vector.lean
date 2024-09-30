import Mathlib.Data.Vector.Basic

open Mathlib

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


abbrev Action := ℕ

abbrev Matrix m n := Vector (Vector Pattern n) m


def lineSpecialization {m n : ℕ}
      (c : Constructor)
      (P : Vector Pattern n)
      (A : Action)
      : Matrix m (c.arity + n - 1) :=
        match n with -- Faz realmente sentido a matriz de padrões ser vazia?
        | 0 => sorry
        | n' + 1 =>
          match P.get 0 with
          | .Wildcard => sorry
          | .Constructor c' ps => sorry
          | .Or p1 p2 => sorry

def specialization
      (c : Constructor)
      (P : Matrix m n)
      (A : Vector Action m)
      : Σ m' : ℕ, Matrix ℕ ℕ Pattern :=

        sorry
