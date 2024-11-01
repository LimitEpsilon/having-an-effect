From Coq Require Import List.
Import ListNotations.

Section Tyenv.
  Universe tyenv_u.
  Definition tyenv : Type@{tyenv_u} := list Type.
End Tyenv.

Section Assign.
  Universe assign_u.
  Definition assign : Type@{assign_u} := list {A & option A}.
End Assign.

Section Filter.
  Universe filter_u.
  Inductive filter : tyenv -> assign -> tyenv -> Type@{filter_u} :=
  | Filter_nil : filter [] [] []
  | Filter_cons_some A a γ σ γ' (FILTER : filter γ σ γ')
    : filter (A :: γ) (existT option A (Some a) :: σ) γ'
  | Filter_cons_none A γ σ γ' (FILTER : filter γ σ γ')
    : filter (A :: γ) (existT option A None :: σ) (A :: γ')
  .
End Filter.

Section Var.
  Universe var_u.
  Inductive var : tyenv -> Type -> Type@{var_u} :=
  | Var_hd {γ A} : var (A :: γ) A
  | Var_tl {γ A B} (x : var γ B) : var (A :: γ) B
  .
End Var.

Section Value.
  Universe value_u.
  Variant value {γ : tyenv} : Type -> Type@{value_u} :=
  | Var {A} (x : var γ A) : value A
  | Val {A} (v : A) : value A
  .
End Value.
Arguments value : clear implicits.

Definition empty_var {A B : Type} (x : var [] A) : B.
Proof.
  exfalso.
  exact (match x in var γ _
    return
      match γ return Prop with
      | [] => False
      | _ :: _ => True
      end
  with
  | Var_hd => I
  | Var_tl _ => I
  end).
Defined.

Definition lift_var Γ : forall {A γ}, var γ A -> var (γ ++ Γ) A :=
  fix go {A γ} x :=
  match γ return var γ A -> var (γ ++ Γ) A with
  | [] => empty_var
  | τ :: τl => fun x =>
    match x in var Aγ B return
      match Aγ with
      | [] => unit
      | A :: γ => var (A :: γ ++ Γ) B
      end
    with
    | Var_hd => Var_hd
    | Var_tl x => Var_tl (go x)
    end
  end x.

Definition lift_value Γ {A γ} (v : value γ A) : value (γ ++ Γ) A :=
  match v with
  | Var x => Var (lift_var Γ x)
  | Val v => Val v
  end.

Definition shift_var {γ A} B (x : var γ A) : var (B :: γ) A :=
  match γ return var γ A -> var (B :: γ) A with
  | [] => empty_var
  | τ :: τl => fun x =>
    match x in var γ' A
      return
        match γ' with
        | [] => unit
        | _ :: _ => var (B :: γ') A
        end
    with
    | Var_hd => Var_tl Var_hd
    | Var_tl x => Var_tl (Var_tl x)
    end
  end x.

Definition shift_value {γ A} B (v : value γ A) : value (B :: γ) A :=
  match v in value _ A return value (B :: γ) A with
  | Var x => Var (shift_var B x)
  | Val v => Val v
  end.

Fixpoint assign_var {A} γ σ γ'
  (FILTER : filter γ σ γ') (x : var γ A) {struct FILTER} : value γ' A :=
  match x in var γ A return filter γ σ γ' -> value γ' A with
  | @Var_hd γ A =>
     let convoy γ A (FILTER : filter (A :: γ) σ γ') :=
       match FILTER in filter Aγ _ γ'
         return
           match Aγ return Type with
           | [] => unit
           | τ :: τl => value γ' τ
           end
       with
       | Filter_nil => tt
       | Filter_cons_some _ v _ _ _ _ => Val v
       | Filter_cons_none _ _ _ _ _ => Var Var_hd
       end
     in
     convoy γ A
  | @Var_tl γ A B x =>
    let convoy γ A B (x : var γ B) (FILTER : filter (A :: γ) σ γ') :=
      match FILTER in filter Aγ _ γ'
        return
          match Aγ return Type with
          | [] => unit
          | τ :: τl => var τl B -> value γ' B
          end
      with
      | Filter_nil => tt
      | Filter_cons_some _ _ γ σ γ' FILTER => fun x_tl =>
        @assign_var B γ σ γ' FILTER x_tl
      | Filter_cons_none A γ σ γ' FILTER => fun x_tl =>
        shift_value A (@assign_var B γ σ γ' FILTER x_tl)
      end x
    in
    convoy γ A B x
  end FILTER.

Definition assign_value {A} γ σ γ'
  (FILTER : filter γ σ γ') (v : value γ A) : value γ' A :=
  match v with
  | @Var _ τ x => assign_var γ σ γ' FILTER x
  | @Val _ τ v' => Val v'
  end.

Lemma shift_assign γ σ γ' (FILTER : filter γ σ γ')
  : forall A B (v : value γ A),
      shift_value B (assign_value γ σ γ' FILTER v) =
      assign_value (B :: γ) (existT option B None :: σ) (B :: γ') (Filter_cons_none _ _ _ _ FILTER) (shift_value B v).
Proof.
  do 3 intro; destruct v.
  - destruct x; reflexivity.
  - reflexivity.
Qed.

Fixpoint id_filter γ : {σ & filter γ σ γ} :=
  match γ with
  | [] => existT (fun σ => filter [] σ []) [] Filter_nil
  | τ :: τl =>
    let (tl, FILTER) := id_filter τl in
    existT (fun σ => filter (τ :: τl) σ (τ :: τl))
      (existT option τ None :: tl)
      (Filter_cons_none τ τl tl τl FILTER)
  end.

