From Coq Require Import ZArith List.
Import ListNotations.

Set Universe Polymorphism.

Module Int.
Class t (T : Type) :=
  {
    one : T;
    succ : T -> T;
    add : T -> T -> T;
    sub : T -> T -> T;
    leb : T -> T -> bool;
    geb : T -> T -> bool;
    ltb : T -> T -> bool;
    gtb : T -> T -> bool;
    eqb : T -> T -> bool;
  }.
End Int.

Module Addr.
Class t (I : Type) `{Int.t I} (T : Type) :=
  {
    one : T;
    succ : T -> T;
    add : T -> T -> T;
    sub : T -> T -> T;
    leb : T -> T -> bool;
    geb : T -> T -> bool;
    ltb : T -> T -> bool;
    gtb : T -> T -> bool;
    eqb : T -> T -> bool;
    of_int : I -> T;
  }.
End Addr.

#[export] Instance IntZ : Int.t Z :=
  {
    one := 1%Z;
    succ := Z.succ;
    add := Z.add;
    sub := Z.sub;
    leb := Z.leb;
    geb := Z.geb;
    ltb := Z.ltb;
    gtb := Z.gtb;
    eqb := Z.eqb;
  }.

#[export, refine] Instance AddrZ : Addr.t Z Z :=
  {
    one := 1%Z;
    succ := Z.succ;
    add := Z.add;
    sub := Z.sub;
    leb := Z.leb;
    geb := Z.geb;
    ltb := Z.ltb;
    gtb := Z.gtb;
    eqb := Z.eqb;
  }.
Proof.
  exact id.
Defined.

Definition int := Z.
Definition addr := Z.

Variant reg : Type -> Type :=
  | PC : reg addr
  | R0 : reg int (* always zero *)
  | R1 : reg int
  | R2 : reg int
  | R3 : reg int
  | R4 : reg int
  | R5 : reg int
  | R6 : reg int
  | R7 : reg int
  | R8 : reg int
  | R9 : reg int
  | R10 : reg int
  | R11 : reg int
  | R12 : reg int
  | R13 : reg int
  | R14 : reg int
  | R15 : reg int
  | R16 : reg int
  | R17 : reg int
  | R18 : reg int
  | R19 : reg int
  | R20 : reg int
  | R21 : reg int
  | R22 : reg int
  | R23 : reg int
  | R24 : reg int
  | R25 : reg int
  | R26 : reg int
  | R27 : reg int
  | R28 : reg int
  | R29 : reg int
  | R30 : reg int
  | R31 : reg int
.

Variant inst : Type :=
  | Inst_add (rd : reg int) (rs1 : reg int) (rs2 : reg int)
  (* add rd rs1 rs2 *)
  (* rd ← (rs1) + (rs2) *)
  | Inst_addi (rd : reg int) (rs1 : reg int) (imm : int)
  (* addi rd rs1 imm *)
  (* rd ← (rs1) + imm *)
  | Inst_ld (rd : reg int) (imm : addr) (rs1 : reg int)
  (* ld rd imm(rs1) *)
  (* rd ← M[(rs1) + imm] *)
  | Inst_st (imm : addr) (rs1 : reg int) (rs2 : reg int)
  (* st imm(rs1) rs2 *)
  (* M[(rs1) + imm] ← (rs2) *)
  | Inst_beq (rs1 : reg int) (rs2 : reg int) (imm : addr)
  (* beq rs1 rs2 imm *)
  (* (pc') = if (rs1) = (rs2) then (pc) + imm else (pc) + 1 *)
  | Inst_blt (rs1 : reg int) (rs2 : reg int) (imm : addr)
  (* blt rs1 rs2 imm *)
  (* (pc') = if (rs1) < (rs2) then (pc) + imm else (pc) + 1 *)
  | Inst_halt
.

Variant mem : Type -> Type :=
  | Imem : mem inst
  | Dmem : mem int
.

(** Defunctionalize *)
(** Meaning : ∀ σ, itree σ *)
Variant fn : Type :=
  | Cycle
.

Variant bop : Type -> Type -> Type -> Type :=
  | Bop_add : bop int int int
  | Bop_eqb : bop int int bool
  | Bop_ltb : bop int int bool
.

Definition tyenv := list Type.

Inductive var : tyenv -> Type -> Type :=
  | Var_hd {γ A} : var (A :: γ) A
  | Var_tl {γ A B} (v : var γ B) : var (A :: γ) B
.

Variant value {γ : tyenv} : Type -> Type :=
  | Var {A} (v : var γ A) : value A
  | Val {A} (v : A) : value A
.

Arguments value : clear implicits.

Variant eff {γ : tyenv} : Type -> Type :=
  | Read_mem {A} (addr : value γ addr) (mem : mem A) : eff A
  | Read_reg {A} (reg : value γ (reg A)) : eff A
  | Write_mem {A} (addr : value γ addr) (mem : mem A) (data : A) : eff unit
  | Write_reg {A} (reg : value γ (reg A)) (data : value γ A) : eff A
  | Bop {A B C} (op : bop A B C) (lop : value γ A) (rop : value γ B) : eff C
  | Vote (tgt : value γ addr) : eff unit
  | Decode (tgt : value γ addr) : eff (option inst)
.

Arguments eff : clear implicits.

Variant branch (itree : tyenv -> Type) {γ : tyenv} : Type -> Type :=
  | Br_cont {A} (cont : itree (A :: γ)) : branch itree A
  | Br_if (con : itree γ) (alt : itree γ) : branch itree bool
  | Br_dec
    (none : itree γ)
    (add : itree (reg int :: reg int :: reg int :: γ))
    (addi : itree (int :: reg int :: reg int :: γ))
    (ld : itree (reg int :: addr :: reg int :: γ))
    (st : itree (reg int :: reg int :: addr :: γ))
    (beq : itree (addr :: reg int :: reg int :: γ))
    (blt : itree (addr :: reg int :: reg int :: γ))
    (halt : itree γ)
    : branch itree (option inst)
.

Arguments branch : clear implicits.

(** γ : the context, not yet determined *)
Inductive itree {γ : tyenv} : Type :=
  | Ret {A} (v : value γ A) : itree
  | Call (f : fn) : itree
  | Unanswered {A} (que : eff γ A) (k : branch (@itree) γ A) : itree
  | Answered {A} (que : eff γ A) (ans : A) (k : itree) : itree
.

Arguments itree : clear implicits.

(* answer : branch itree σ A -> A -> itree σ *)
(* for var σ A, either shift or change to value *)
(* relation between σ and {A & option A} *)

(*Definition entry := {A & option A}.*)
(*Definition x : entry := existT option int None.*)

Definition assign := list {A & option A}.

Notation "'∃?' A x" := (existT option A x)
  (at level 10, A at next level, x at next level).

Fixpoint unassigned (σ : assign) : tyenv :=
  match σ with
  | [] => []
  | existT _ A None :: tl => A :: unassigned tl
  | existT _ _ (Some _) :: tl => unassigned tl
  end.

Fixpoint tyenv_of_assign (σ : assign) : tyenv :=
  match σ with
  | [] => []
  | t :: tl =>
    let τ := match t with existT _ τ _ => τ end in
    τ :: tyenv_of_assign tl
  end.

Fixpoint assign_of_tyenv (γ : tyenv) : assign :=
  match γ with
  | [] => []
  | A :: tl => ∃? A None :: assign_of_tyenv tl
  end.

Lemma unassigned_assign γ : γ = unassigned (assign_of_tyenv γ).
Proof.
  induction γ; simpl in *; f_equal; auto.
Qed.

#[local] Definition add_dummy {γ A} B (v : value γ A) : value (B :: γ) A.
Proof.
  destruct v.
  - destruct γ.
    + abstract (inversion v).
    + refine (match v in var (_ :: _) _ with
      | Var_hd => _ | Var_tl x => _
      end).
      * exact (Var (Var_tl Var_hd)).
      * exact (Var (Var_tl (Var_tl x))).
  - exact (Val v).
Defined.

Definition empty_var {A B : Type} (v : var [] A) : B.
Proof. inversion v. Qed.

Definition assign_var {A} :
  forall (σ : assign) (x : var (tyenv_of_assign σ) A), value (unassigned σ) A.
Proof.
  refine (fix go σ x' {struct σ} :=
  match σ as σ' return var (tyenv_of_assign σ') A -> value (unassigned σ') A with
  | [] => empty_var
  | hd :: tl =>
    match hd as hd' return
      var (tyenv_of_assign (hd' :: tl)) A -> value (unassigned (hd' :: tl)) A with
    | existT _ T' v' =>
      let convoy T v (x : var (T :: tyenv_of_assign tl) A)
        : value (unassigned (∃? T v :: tl)) A := _ in
      convoy T' v'
    end
  end x').
  destruct v as [v|].
  - refine (match x in var (τ :: τl) B return
      forall (RRτ : τ = T) (RRτl : τl = tyenv_of_assign tl) (RRB : B = A), _ with
    | @Var_hd _ τ => _ | @Var_tl _ τ B x => _
    end eq_refl eq_refl eq_refl); intros.
    + rewrite RRτ. exact (Val v).
    + set (go' := go tl).
      rewrite <- RRB, <- RRτl in go'.
      exact (go' x).
  - refine (match x in var (τ :: τl) B return
      forall (RRτ : τ = T) (RRτl : τl = tyenv_of_assign tl) (RRB : B = A), _ with
    | @Var_hd _ τ => _ | @Var_tl _ τ B x => _
    end eq_refl eq_refl eq_refl); intros.
    + rewrite RRτ. exact (Var Var_hd).
    + set (go' := go tl).
      rewrite <- RRτl, <- RRB in go'.
      rewrite RRτ. exact (add_dummy T (go' x)).
Defined.

Compute assign_var [∃? bool None; ∃? _ (Some 1); ∃? int None] (Var_tl Var_hd).

Definition assign_value {A}
  (σ : assign) (v : value (tyenv_of_assign σ) A) :
  value (unassigned σ) A.
Proof.
  destruct v as [τ|τ].
  - apply assign_var. assumption.
  - exact (Val v).
Defined.

Lemma assign_head {A} (v : A) (γ : tyenv) :
  match unassigned_assign γ in _ = T return value T A -> value γ A with
  | eq_refl => id
  end (assign_var (∃? A (Some v) :: assign_of_tyenv γ) Var_hd) = @Val γ A v.
Proof.
  rewrite (unassigned_assign γ). reflexivity.
Qed.


