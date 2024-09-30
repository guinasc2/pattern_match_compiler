import Mathlib.Data.Vector.Basic

-- set_option autoImplicit false

open Mathlib

structure Constr where
  name : String
  arity : ℕ
  deriving DecidableEq, Repr

instance : Repr Constr where
  reprPrec c _n := c.name ++ " " ++ toString c.arity

def exConstr1 : Constr := Constr.mk "List.nil" 0
def exConstr2 : Constr := Constr.mk "List.cons" 2

#eval exConstr1
#eval exConstr2


inductive Val where
| Constr : Constr → List Val → Val
deriving Repr

inductive Pat where
| Wild : Pat
| Constr : Constr → List Pat → Pat
| Or: Pat → Pat → Pat
deriving Repr

-- instance : Repr Pat where
--   reprPrec p n :=
--     match p with
--     | .Wild => "_"
--     | .Constr c ps => repr c ++ " " ++ repr ps
--     | .Or p1 p2 => reprPrec p1 n ++ " | " ++ reprPrec p2 n

def exPat1 : Pat := Pat.Constr exConstr1 []
def exPat2 : Pat := Pat.Constr exConstr2 [Pat.Wild, Pat.Wild]

#eval Pat.Wild
#eval Pat.Or Pat.Wild Pat.Wild
#eval exPat1
#eval exPat2


def instOf (p : Pat) (v : Val) : Bool :=
  match p with
  | .Wild => true
  | .Or p1 p2 => instOf p1 v || instOf p2 v
  | .Constr c ps =>
    match v with
    | .Constr n vs =>
      match decEq c n with
      | isFalse _ => false
      | isTrue _ =>
        match ps, vs with
        | [], [] => true
        | [], _ => false
        | _, [] => false
        | .cons p' ps', .cons v' vs' =>
          instOf p' v' && instOf (Pat.Constr c ps') (Val.Constr n vs')

def listInstOf (ps : List Pat) (vs : List Val) : Bool :=
  List.and (List.zipWith instOf ps vs)


abbrev Action := ℕ
abbrev Matrix α := List (List α)
abbrev ClauseMatrix := Matrix Pat × List Action


def exMatrix : Matrix Pat := [
  [exPat1, Pat.Wild],
  [Pat.Wild, exPat1],
  [exPat2, exPat2]
  ]

def exMatrix2 : Matrix Pat := [
  [exPat1, Pat.Wild],
  [Pat.Wild, exPat1],
  [Pat.Wild, Pat.Wild]
  ]

def exActions : List Action := [1, 2, 3]


def MLmatch (vs : List Val) (M : ClauseMatrix) : Option Action :=
  match M with
  | ⟨ MP, A ⟩ =>
    match MP, A with
    | ps :: ps', a :: as =>
      match listInstOf ps vs with
      | true => a
      | false => MLmatch vs (ps', as)
    | _, _ => none


def countConstrs (p : Pat) : ℕ :=
  match p with
  | .Wild => 0
  | .Constr _ _ => 1
  | .Or p1 p2 => countConstrs p1 + countConstrs p2

def countConstrsLine (ps : List Pat) : ℕ :=
  match ps with
  | [] => 0
  | p :: ps' => countConstrs p + countConstrsLine ps'

def countConstrsMatrix (M : ClauseMatrix) : ℕ :=
  match M with
  | ⟨MP, A⟩ =>
    match MP, A with
    | [], _ => 0
    | l :: ls, _a :: as =>
      match l with
      | [] => 0
      | _p :: _ps =>
        countConstrsLine l + countConstrsMatrix (ls, as)
    | _, _ => 0

#eval exMatrix
#eval countConstrsMatrix (exMatrix, exActions)


/-
  Matrix Decomposition
-/

instance : Append ClauseMatrix where
  append a b := (a.1 ++ b.1, a.2 ++ b.2)

def lineSpec
      (c : Constr)
      (P : List Pat)
      (a : Action)
      : Option (ClauseMatrix) :=
        match P with
        | [] => none
        | p :: ps =>
          match p with
          | .Wild => ([(List.replicate c.arity Pat.Wild) ++ ps], [a])
          | .Constr c' ps' =>
            match decEq c c' with
            | isFalse _ => none
            -- No caso do isTrue, acho que deveria pegar as variáveis, mas elas foram abstraídas para _
            -- No próprio ex do merge do artigo parece acontecer isso
            | isTrue _ => ([ps' ++ ps], [a])
          | .Or p1 p2 =>
            let m1 := lineSpec c (p1 :: ps) a
            let m2 := lineSpec c (p2 :: ps) a
            match m1, m2 with
            | none, none => none
            | some m1, none => m1
            | none, some m2 => m2
            | some m1, some m2 => m1 ++ m2

def spec (c : Constr) (M : ClauseMatrix) : ClauseMatrix :=
  match M with
  | ⟨MP, A⟩ =>
    match MP, A with
    | l :: ls, a :: as =>
      let newLine := lineSpec c l a
      match newLine with
      | none => spec c (ls, as)
      | some x => x ++ spec c (ls, as)
    | _, _ => ([], [])

#eval spec exConstr1 (exMatrix, exActions)
#eval spec exConstr2 (exMatrix, exActions)

#eval spec exConstr1 (exMatrix2, exActions)
#eval spec exConstr2 (exMatrix2, exActions)


def instOfConst (p : Pat) (c : Constr) : Bool :=
  match p with
  | .Wild => true
  | .Or p1 p2 => instOfConst p1 c || instOfConst p2 c
  | .Constr c' _ps => c = c'


def instInduction (P : Pat → Prop)
  (p : Pat)
  (c : Constr)
  (wild : ∀ p, p = Pat.Wild → P p)
  (constr : ∀ p ps, p = Pat.Constr c ps → P p)
  (or : ∀ p p1 p2, p = Pat.Or p1 p2 → P p1 → P p2 → P p)
  : P p :=
    match p with
    | Pat.Wild => wild Pat.Wild rfl
    | Pat.Constr c' ps => constr (Pat.Constr c' ps) ps
    | Pat.Or p1 p2 =>
      or (Pat.Or p1 p2) p1 p2 rfl (instInduction P p1 c wild constr or) (instInduction P p2 c wild constr or)

#print Pat.rec
lemma teste :
  ∀ p c ls a, instOfConst p c = true → lineSpec c (p::ls) a ≠ none := by
    -- intros p
    -- induction p with
    -- | Wild =>
    --   intros c ls a H
    --   simp [lineSpec.eq_def]
    -- | Constr c' ps =>
    --   intros c ls a H
    --   simp [lineSpec.eq_def]
    --   split
    --   simp [instOfConst] at H
    --   contradiction
    --   simp
    -- | Or p1 p2 =>
    --   intros c ls a H

    --   sorry
    -- apply (Pat.rec _ (λ ps => ∀ p, p ∈ ps → instOfConst p c = true → lineSpec c (p::ls) a ≠ none))
    apply Pat.rec
    ·
      intros c ls a H
      simp [lineSpec]
    ·
      intros c ps m c' ps' a H
      simp [lineSpec]
      split
      simp [instOfConst] at H
      contradiction
      simp
    ·
      intros p1 p2 IH1 IH2 c ps a H
      simp [lineSpec]
      split
      ·
        simp [instOfConst] at H
        rcases H with H | H
        have t := IH1 c ps a H
        contradiction
        have t := IH2 c ps a H
        contradiction
      ·
        simp
      ·
        simp
      ·
        simp
    ·
      sorry
    ·
      intros p ps H H1
      sorry
    ·
      sorry


lemma lineSpecEmpty :
  ∀ c l ls a, instOfConst l c = true → ∃ x xs as, lineSpec c (l::ls) a = some (x::xs, as) := by
    intros c l ls a
    rw [lineSpec.eq_def]
    simp
    cases l
    ·
      simp
    ·
      rename_i c' ps
      intros H
      simp
      split
      <;> simp [instOfConst] at H
      contradiction
      exists List.replicate c.arity Pat.Wild ++ ls
      exists []
      exists [a]
    ·
      rename_i p1 p2
      simp
      split
      intros H
      rw [lineSpec.eq_def] at *
      simp [instOfConst] at *
      cases H
      repeat sorry

lemma lineSpecReduces :
  ∀ l c a,
    lineSpec c l a = some x →
    countConstrsMatrix x < countConstrsLine l := by
      intros l
      induction l with
      | nil =>
        intros c a H
        simp [lineSpec] at *
      | cons l' ls IH =>
        intros c a H
        simp [lineSpec, countConstrsLine]
        sorry


lemma specReduces : ∀ m c, countConstrsMatrix (spec c m) < countConstrsMatrix m := by
  intros m c
  sorry

-----------------------------------------------------------
-----------------------------------------------------------

def lineDefault
      (P : List Pat)
      (a : Action)
      : Option ClauseMatrix :=
        match P with
        | [] => none
        | p :: ps =>
          match p with
          | .Wild => ([ps], [a])
          | .Constr _c' _ps' => none
          | .Or p1 p2 =>
            let m1 := lineDefault (p1 :: ps) a
            let m2 := lineDefault (p2 :: ps) a
            match m1, m2 with
            | none, none => none
            | some m1, none => m1
            | none, some m2 => m2
            | some m1, some m2 => m1 ++ m2

def default
      (M : ClauseMatrix)
      : ClauseMatrix :=
        match M with
        | ⟨MP, A⟩ =>
          match MP, A with
          | l :: ls, a :: as =>
            let newLine := lineDefault l a
            match newLine with
            | none => default (ls, as)
            | some x => x ++ default (ls, as)
          | _, _ => ([], [])

#eval default (exMatrix, exActions)

#eval default (exMatrix2, exActions)


-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------

/-
  Decision Trees
-/


-- Daria pra representar isso como List Int?
inductive Occurrence where
| Empty : Occurrence
| Sequence : ℤ → Occurrence → Occurrence

inductive DecisionTree where
| Leaf : Action → DecisionTree
| Fail : DecisionTree
| Switch : List (Constr × DecisionTree) → DecisionTree
| Swap : Int → DecisionTree → DecisionTree
deriving Repr

inductive GeneralizedPat where
| Pat : Constr → GeneralizedPat
| Or : Pat → GeneralizedPat → GeneralizedPat


def allWild (ps : List Pat) : Bool :=
  match ps with
  | [] => true
  | p :: ps' =>
    match p with
    | .Wild => allWild ps'
    | _ => false

def swapLine (n : ℕ) (l : List α) : List α :=
  match l with
  | [] => []
  | (l' :: ls) =>
    have x : Fin (l'::ls).length := Fin.ofNat 0
    have x' : Fin (l'::ls).length := Fin.ofNat n
    have i := List.get (l'::ls) x
    have i' := List.get (l'::ls) x'
    List.set (List.set (l'::ls) x i') x' i

def swapColumn (n : ℕ) (l : Matrix α) : Matrix α :=
  List.transpose (swapLine n (List.transpose l))


def findColumn (M : Matrix Pat) : ℕ :=
  -- aqui assume que a matriz é transposta
  match M with
  | [] => 1
  | l :: ls =>
    match allWild l with
    | true => 1 + findColumn ls
    | false => 0


def getConstr (p : Pat) : List Constr :=
  match p with
  | .Wild => []
  | .Constr c _ps => [c]
  | .Or p1 p2 => getConstr p1 ++ getConstr p2

def collectHeadMatrix (m : Matrix Pat) : List Constr :=
  match m with
  | [] => []
  | l :: ls =>
    match l with
    | [] => []
    | p :: _ps =>
      getConstr p ++ collectHeadMatrix ls


#eval exMatrix
#eval collectHeadMatrix exMatrix


def CompilationScheme (o : List Occurrence) (M : ClauseMatrix) : DecisionTree :=
  match M with
  | ⟨ MP, A ⟩ =>
    match MP, A with
    | [], [] => .Fail -- m = 0
    | l :: ls, a :: as =>
      match allWild l with
      | true => .Leaf a -- m > 0; primeira linha tem apenas _
      | false =>
        match l with
        | [] => .Leaf a -- m > 0; n = 0
        | p :: ps => -- m > 0; n > 0
          let i := findColumn (List.transpose (l::ls))
          let m' := match i with
                      | 0 => l::ls -- primeira coluna
                      | n => swapColumn n (l::ls) -- coluna i > 0, faz a troca

          let S := collectHeadMatrix m'
          let Mk := List.map (flip spec (m', a::as)) S
          -- TODO: S deve ter elementos distintos
          -- TODO: Precisa incluir a matriz default se S não for uma assinatura
          -- Como checar se S é um assinatura?

          -- TODO: Ak precisa mudar
          --    trocar o₁ por o₁·1 ... o₁·a
          let Ak := List.map (CompilationScheme o) Mk

          let L := List.zip S Ak

          match i with
          | 0 => .Switch L
          | n => .Swap n (.Switch L)
    -- Se tiver linha na matriz, mas não tiver ação para tomar, tem erro na entrada
    -- Acho que, dada uma entrada correta, nunca deveria chegar aqui
    -- Entrada correta: número de linhas da matriz = número de ações
    | _, _ => .Fail
  -- termination_by
  --   countConstrsMatrix M
  -- decreasing_by
  --   simp [countConstrsMatrix]
  --   obtain ⟨MP, A⟩ := M
  --   simp_wf
  --   sorry
