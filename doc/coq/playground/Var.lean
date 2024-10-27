def tyenv.{u} := List (Type u)
def assign.{u} := List (Σ a : Type u, Option a)

inductive dummy.{u} : Type u :=
| intro

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
    let convoy {γ} (x : var γ A) :
      match γ with
      | [] => False
      | _ :: _ => True
    :=
    match x with
    | .Var_hd => True.intro
    | .Var_tl _ => True.intro
    convoy x
  )

def shift_value {γ A} B (v : value γ A) : value (B :: γ) A :=
  match v with
  | .Var x =>
    match γ with
    | [] => empty_var x
    | _τ :: _τl =>
      match x with
      | .Var_hd => value.Var (var.Var_tl var.Var_hd)
      | .Var_tl x => value.Var (var.Var_tl (var.Var_tl x))
  | .Val v => value.Val v

def assign_var {A} γ σ γ' (FILTER : filter γ σ γ') (x : var γ A) : value γ' A :=
  match x with
  | .Var_hd =>
    let convoy {Aγ} (FILTER' : filter Aγ σ γ') :
      match Aγ with
      | [] => dummy
      | A :: _γ => value γ' A
    :=
      match FILTER' with
      | .Filter_nil => dummy.intro
      | .Filter_cons_some _A v _γ _σ _γ' _FILTER => id (value.Val v)
      | .Filter_cons_none _A _γ _σ _γ' _FILTER => id (value.Var var.Var_hd)
    convoy FILTER
  | .Var_tl x =>
    let convoy {Aγ} (FILTER' : filter Aγ σ γ') :
      match Aγ with
      | [] => dummy
      | _τ :: τl => ∀ {B}, var τl B -> value γ' B
    :=
      match FILTER' with
      | .Filter_nil => dummy.intro
      | .Filter_cons_some _A _v γ_tl σ_tl γ'_tl FILTER'_tl => fun {B} x_tl =>
        id (@assign_var B γ_tl σ_tl γ'_tl FILTER'_tl x_tl)
      | .Filter_cons_none A' γ_tl σ_tl γ'_tl FILTER'_tl => fun {B} x_tl =>
        id (shift_value A' (@assign_var B γ_tl σ_tl γ'_tl FILTER'_tl x_tl))
    convoy FILTER x

def assign_value {A} γ σ γ' (FILTER : filter γ σ γ') (v : value γ A) : value γ' A :=
  match v with
  | .Var x => assign_var γ σ γ' FILTER x
  | .Val v => value.Val v

def id_filter γ : Σ σ, filter γ σ γ :=
  match γ with
  | [] => ⟨[], filter.Filter_nil⟩
  | τ :: τl =>
    let ⟨tl, FILTER⟩ := id_filter τl
    ⟨⟨τ, none⟩ :: tl, filter.Filter_cons_none τ τl tl τl FILTER⟩

