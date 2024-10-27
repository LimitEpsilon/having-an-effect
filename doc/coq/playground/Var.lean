def tyenv.{u} := List (Type u)
def assign.{u} := List (Σ a : Type u, Option a)

inductive filter.{u} : tyenv → assign → tyenv → Type (u + 1) :=
| Filter_nil : filter [] [] []
| Filter_cons_some A a γ σ γ' (FILTER : filter γ σ γ')
  : filter (A :: γ) (⟨A, some a⟩ :: σ) γ'
| Filter_cons_none A γ σ γ' (FILTER : filter γ σ γ')
  : filter (A :: γ) (⟨A, none⟩ :: σ) (A :: γ')

inductive var.{u} : tyenv → Type → Type (u + 1) :=
| Var_hd {γ A} : var (A :: γ) A
| Var_tl {γ A B} (x : var γ B) : var (A :: γ) B

inductive value.{u} : tyenv → Type → Type (u + 1) :=
| Var {γ A} (x : var γ A) : value γ A
| Val {γ A} (v : A) : value γ A

def empty_var {A B} (x : var [] A) : B :=
  False.elim (
    let convoy {γ} (x : var γ A)
    : match γ with
      | [] => False
      | _ :: _ => True
    :=
    match x with
    | .Var_hd => True.intro
    | .Var_tl _x_tl => True.intro
    convoy x
  )

def shift_value {γ A} B (v : value γ A) : value (B :: γ) A :=
  open var value in
  match v with
  | .Var x =>
    match γ with
    | [] => empty_var x
    | _τ :: _τl =>
      match x with
      | .Var_hd => Var (Var_tl Var_hd)
      | .Var_tl x_tl => Var (Var_tl (Var_tl x_tl))
  | .Val v => value.Val v

def assign_var {A} γ σ γ' (FILTER : filter γ σ γ') (x : var γ A) : value γ' A :=
  open var value in
  match x with
  | .Var_hd =>
    match FILTER with
    | .Filter_cons_some _A v _γ _σ _γ' _FILTER => Val v
    | .Filter_cons_none _A _γ _σ _γ' _FILTER => Var Var_hd
  | .Var_tl x_tl =>
    match FILTER with
    | .Filter_cons_some _A _v γ_tl σ_tl γ'_tl FILTER_tl =>
      assign_var γ_tl σ_tl γ'_tl FILTER_tl x_tl
    | .Filter_cons_none A_hd γ_tl σ_tl γ'_tl FILTER_tl =>
      shift_value A_hd (assign_var γ_tl σ_tl γ'_tl FILTER_tl x_tl)

def assign_value {A} γ σ γ' (FILTER : filter γ σ γ') (v : value γ A) : value γ' A :=
  open value in
  match v with
  | .Var x => assign_var γ σ γ' FILTER x
  | .Val v => Val v

def id_filter γ : Σ σ, filter γ σ γ :=
  open filter in
  match γ with
  | [] => ⟨[], Filter_nil⟩
  | τ :: τl =>
    let ⟨tl, FILTER⟩ := id_filter τl
    ⟨⟨τ, none⟩ :: tl, Filter_cons_none τ τl tl τl FILTER⟩

