import Mathlib.Data.Vector.Basic

-- set_option autoImplicit false

open Mathlib

structure Constr where
  name : String
  arity : ℕ
  ty : String
  deriving DecidableEq, Repr

instance : Repr Constr where
  reprPrec c _n := c.ty ++ "." ++ c.name ++ " " ++ toString c.arity

def exConstr1 : Constr := Constr.mk "nil" 0 "List"
def exConstr2 : Constr := Constr.mk "cons" 2 "List"

#eval exConstr1
#eval exConstr2


abbrev Ctx := Std.HashMap String (List Constr)


def sig (t : List Constr) (ctx : Ctx) : Bool :=
  match t with
  | [] => False
  | t' =>
    match List.map (λ x => x.ty) t' with
    | [c] =>
      match ctx[c]? with
      | some x => List.isPerm t x
      | none => False
    | _ => False


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


def exMatrix : Matrix Pat := [[exPat1, Pat.Wild], [Pat.Wild, exPat1], [exPat2, exPat2]]
def exMatrix2 : Matrix Pat := [[exPat1, Pat.Wild], [Pat.Wild, exPat1], [Pat.Wild, Pat.Wild]]

def exActions : List Action := [1, 2, 3]

def exClause1 : ClauseMatrix := (exMatrix, exActions)
def exClause2 : ClauseMatrix := (exMatrix2, exActions)


def MLmatch (vs : List Val) (M : ClauseMatrix) : Option Action :=
  match M with
  | ⟨ MP, A ⟩ =>
    match MP, A with
    | ps :: ps', a :: as =>
      match listInstOf ps vs with
      | true => a
      | false => MLmatch vs (ps', as)
    | _, _ => none


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
            | isTrue _ => ([ps' ++ ps], [a])
          | .Or p1 p2 =>
            let m1 := lineSpec c (p1 :: ps) a
            let m2 := lineSpec c (p2 :: ps) a
            match m1, m2 with
            | none, none => none
            | some m1', none => m1'
            | none, some m2' => m2'
            | some m1', some m2' => m1' ++ m2'

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


#eval spec exConstr1 exClause1
#eval spec exConstr2 exClause1
#eval spec exConstr1 exClause2
#eval spec exConstr2 exClause2


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
            | some m1', none => m1'
            | none, some m2' => m2'
            | some m1', some m2' => m1' ++ m2'

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


#eval default exClause1
#eval default exClause2


-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------

/-
  Decision Trees
-/


abbrev Occurrence := List Val

inductive DecisionTree where
| Leaf : Action → DecisionTree
| Fail : DecisionTree
| Switch : Val → List (Constr × DecisionTree) → DecisionTree
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
    -- TODO: tá avalidando ps' duas vezes. Como melhorar?
    -- Lean reclamou disso:
    -- allWild [p1, p2] && allWild ps'
    | .Or p1 p2 => allWild (p1::ps') && allWild (p2::ps')
    | _ => false

def swapLine (n : ℕ) (l : List α) : List α :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | n, (l' :: ls) =>
    have x : Fin (l'::ls).length := Fin.ofNat 0
    have x' : Fin (l'::ls).length := Fin.ofNat n
    have i := List.get (l'::ls) x
    have i' := List.get (l'::ls) x'
    List.set (List.set (l'::ls) x i') x' i

def swapColumn (n : ℕ) (l : Matrix α) : Matrix α :=
  match n with
  | 0 => l
  | _ => List.transpose (swapLine n (List.transpose l))


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



mutual
  def countConstrs (p : Pat) : ℕ :=
    match p with
    | .Wild => 0
    | .Constr _ ps => 1 + countConstrsLine ps
    | .Or p1 p2 => countConstrs p1 + countConstrs p2

  def countConstrsLine (ps : List Pat) : ℕ :=
    match ps with
    | [] => 0
    | p :: ps' => countConstrs p + countConstrsLine ps'
end

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

mutual
  def procOr (M : ClauseMatrix) : ClauseMatrix :=
    match M with
    | ⟨MP, A⟩ =>
      match MP, A with
      | l::ls, a::as => lineProcOr l a ++ procOr (ls, as)
      | _, _ => ([], [])

  def lineProcOr (ps : List Pat) (a : Action) : ClauseMatrix :=
    match ps with
    | [] => ([], [])
    | (.Or p1 p2)::ps' => lineProcOr (p1::ps') a ++ lineProcOr (p2::ps') A
    | ps => ([ps], [a])
end

lemma specReduces : ∀ m c, m.1 ≠ [] → countConstrsMatrix (spec c m) < countConstrsMatrix (procOr m) := by
  intros m c H
  obtain ⟨m, as⟩ := m
  induction m with
  | nil =>
    contradiction
  | cons l ls IH =>
    sorry



def CompilationScheme (ctx : Ctx) (os : Occurrence) (M : ClauseMatrix) : DecisionTree :=
  match M with
  | ⟨ MP, A ⟩ =>
    match os, MP, A with
    | _, [], [] => .Fail -- m = 0
    | o :: os', l :: ls, a :: as =>
      match allWild l with
      | true => .Leaf a -- m > 0; primeira linha tem apenas _
      | false =>
        match l with
        | [] => .Leaf a -- m > 0; n = 0
        | p :: ps => -- m > 0; n > 0

          let i := findColumn (List.transpose (l::ls))
          let m' := swapColumn i (l::ls) -- coluna i > 0, faz a troca
          let o' := swapLine i (o::os') -- coluna i > 0, faz a troca

          -- valeria mais a pena só não inserir elementos repetidos?
          let S := List.eraseDups (collectHeadMatrix m')
          let x := sig S ctx

          let Mk := if x then List.map (flip spec (m', a::as)) S
                    else List.map (flip spec (m', a::as)) S ++ [default (m', a::as)]
          let S' := if x then S
                    else S ++ [Constr.mk "*" 0 "default"]

          let Ak := match o' with
                    -- Isso não deveria acontecer
                    -- Não acho que essa seja a melhor solução
                    | [] => []
                    -- | [] => Lean.throwError "Isso não deveria acontecer"
                    | (.Constr _ ps)::os'' => List.map (CompilationScheme ctx (ps ++ os'')) Mk

          let L := List.zip S' Ak

          match i with
          | 0 => .Switch o L
          | n => .Swap (n+1) (.Switch o L)

    -- Se tiver linha na matriz, mas não tiver ação para tomar, tem erro na entrada
    -- Acho que, dada uma entrada correta, nunca deveria chegar aqui
    -- Entrada correta: número de linhas da matriz = número de ações
    | _, _, _ => .Fail
  -- termination_by
  --   countConstrsMatrix M
  -- decreasing_by
  --   simp [countConstrsMatrix]
  --   obtain ⟨MP, A⟩ := M
  --   simp_wf
  --   sorry
