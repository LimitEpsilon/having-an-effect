From Coq Require Import ZArith List.
From Playground Require Import Var.
Import ListNotations.

Set Printing Universes.

Section Int.
  Universe int_u.
  Definition int : Type@{int_u} := Z.
End Int.

Section Bool.
  Universe bool_u.
  Definition bool : Type@{bool_u} := bool.
End Bool.

Section Addr.
  Universe addr_u.
  Definition addr : Type@{addr_u} := Z.
End Addr.

Section Reg.
  (* add here *)
  Universe reg_u.
  Variant reg : Type -> Type@{reg_u} :=
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
End Reg.

Section Inst.
  (* add here *)
  Universe inst_u.
  Variant inst : Type@{inst_u} :=
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
End Inst.

Section Mem.
  Universe mem_u.
  Variant mem : Type -> Type@{mem_u} :=
  | Imem : mem inst
  | Dmem : mem int
  .
End Mem.

Section Fn.
  (** Defunctionalize *)
  (** Meaning : ∀ γ, itree γ *)
  (* add here *)
  Universe fn_u.
  Variant fn : Type@{fn_u} :=
  | Cycle
  .
End Fn.

Section Bop.
  (* add here *)
  Universe bop_u.
  Variant bop : Type -> Type -> Type -> Type@{bop_u} :=
  | Bop_add : bop int int int
  | Bop_eqb : bop int int bool
  | Bop_ltb : bop int int bool
  .
End Bop.

Section Eff.
  (* add here *)
  Universe eff_u.
  Variant eff {γ : tyenv} : Type -> Type@{eff_u} :=
  | Read_mem {A} (addr : value γ addr) (mem : mem A) : eff A
  | Read_reg {A} (reg : value γ (reg A)) : eff A
  | Write_mem {A} (addr : value γ addr) (mem : mem A) (data : A) : eff unit
  | Write_reg {A} (reg : value γ (reg A)) (data : value γ A) : eff unit
  | Bop {A B C} (op : bop A B C) (lop : value γ A) (rop : value γ B) : eff C
  | Vote (tgt : value γ addr) : eff unit
  | Decode (tgt : value γ addr) : eff (option inst)
  .
End Eff.
Arguments eff : clear implicits.

Section Branch.
  (* add here *)
  Universe branch_u.
  Variant branch {itree : tyenv -> Type} {γ : tyenv} : Type -> Type@{branch_u} :=
  | Br_cont {A} (cont : itree (A :: γ)) : branch A
  | Br_if (con : itree γ) (alt : itree γ) : branch bool
  | Br_dec
    (none : itree γ)
    (add : itree (reg int :: reg int :: reg int :: γ))
    (addi : itree (int :: reg int :: reg int :: γ))
    (ld : itree (reg int :: addr :: reg int :: γ))
    (st : itree (reg int :: reg int :: addr :: γ))
    (beq : itree (addr :: reg int :: reg int :: γ))
    (blt : itree (addr :: reg int :: reg int :: γ))
    (halt : itree γ)
    : branch (option inst)
  .
End Branch.
Arguments branch : clear implicits.

Section Itree.
  (** γ : the context, not yet determined *)
  Universe itree_u.
  Inductive itree {γ : tyenv} : Type@{itree_u} :=
  | Ret {A} (v : value γ A) : itree
  | Call (f : fn) : itree
  | Unanswered {A} (que : eff γ A) (k : branch (@itree) γ A) : itree
  | Answered {A} (que : eff γ A) (ans : A) (k : itree) : itree
  .
End Itree.
Arguments itree : clear implicits.

Unset Printing Universes.

Notation "'∃?' A x" := (existT option A x)
  (at level 10, A at next level, x at next level).

Definition assign_eff {A} γ σ γ'
  (FILTER : filter γ σ γ') (e : eff γ A) : eff γ' A.
Proof.
  destruct e.
  - econstructor 1; eauto using assign_value.
  - econstructor 2; eauto using assign_value.
  - econstructor 3; eauto using assign_value.
  - econstructor 4; eauto using assign_value.
  - econstructor 5; eauto using assign_value.
  - econstructor 6; eauto using assign_value.
  - econstructor 7; eauto using assign_value.
Defined.

Ltac t := repeat econstructor; eauto.

Definition assign_branch
  (assign_itree : forall γ σ γ', filter γ σ γ' -> itree γ -> itree γ')
  {A} γ σ γ'
  (FILTER : filter γ σ γ') (br : branch itree γ A) : branch itree γ' A.
Proof.
  refine (
  match br in branch _ _ A return branch itree _ A with
  | Br_cont cont =>
    Br_cont
      (assign_itree (_ :: γ) (∃? _ None :: σ) (_ :: γ') _ cont)
  | Br_if con alt =>
    Br_if
      (assign_itree γ σ γ' FILTER con)
      (assign_itree γ σ γ' FILTER alt)
  | Br_dec none add addi ld st beq blt halt =>
    Br_dec
      (assign_itree γ σ γ' FILTER none)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ add)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ addi)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ ld)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ st)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ beq)
      (assign_itree (_ :: _ :: _ :: γ) (∃? _ None :: ∃? _ None :: ∃? _ None :: σ) (_ :: _ :: _ :: γ') _ blt)
      (assign_itree γ σ γ' FILTER halt)
  end); t.
Defined.

Definition assign_itree
  : forall γ σ γ', filter γ σ γ' -> itree γ -> itree γ' :=
  fix go γ σ γ' FILTER t :=
  match t with
  | Ret v => Ret (assign_value γ σ γ' FILTER v)
  | Call f => Call f
  | Unanswered que k =>
    Unanswered (assign_eff γ σ γ' FILTER que) (assign_branch go γ σ γ' FILTER k)
  | Answered que ans k =>
    Answered (assign_eff γ σ γ' FILTER que) ans (go γ σ γ' FILTER k)
  end.

Definition br_cont {A} γ σ γ' (FILTER : filter γ σ γ')
  (cont : itree (A :: γ))
  : A -> itree γ'.
Proof.
  refine (fun ans =>
  assign_itree (_ :: γ) (∃? _ (Some ans) :: σ) γ' _ cont); t.
Defined.

Definition br_if γ σ γ' (FILTER : filter γ σ γ')
  (con : itree γ)
  (alt : itree γ)
  : bool -> itree γ'.
Proof.
  refine (fun ans =>
  if ans
  then assign_itree γ σ γ' _ con
  else assign_itree γ σ γ' _ alt); t.
Defined.

Definition br_dec γ σ γ' (FILTER : filter γ σ γ')
  (none : itree γ)
  (add : itree (reg int :: reg int :: reg int :: γ))
  (addi : itree (int :: reg int :: reg int :: γ))
  (ld : itree (reg int :: addr :: reg int :: γ))
  (st : itree (reg int :: reg int :: addr :: γ))
  (beq : itree (addr :: reg int :: reg int :: γ))
  (blt : itree (addr :: reg int :: reg int :: γ))
  (halt : itree γ)
  : option inst -> itree γ'.
Proof.
  refine (fun ans =>
  match ans with
  | None => assign_itree γ σ γ' _ none
  | Some (Inst_add rd rs1 rs2) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some rs2) :: ∃? _ (Some rs1) :: ∃? _ (Some rd) :: σ) γ' _ add
  | Some (Inst_addi rd rs1 imm) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some imm) :: ∃? _ (Some rs1) :: ∃? _ (Some rd) :: σ) γ' _ addi
  | Some (Inst_ld rd imm rs1) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some rs1) :: ∃? _ (Some imm) :: ∃? _ (Some rd) :: σ) γ' _ ld
  | Some (Inst_st imm rs1 rs2) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some rs2) :: ∃? _ (Some rs1) :: ∃? _ (Some imm) :: σ) γ' _ st
  | Some (Inst_beq rs1 rs2 imm) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some imm) :: ∃? _ (Some rs2) :: ∃? _ (Some rs1) :: σ) γ' _ beq
  | Some (Inst_blt rs1 rs2 imm) =>
    assign_itree (_ :: _ :: _ :: γ) (∃? _ (Some imm) :: ∃? _ (Some rs2) :: ∃? _ (Some rs1) :: σ) γ' _ blt
  | Some Inst_halt =>
    assign_itree γ σ γ' _ halt
  end); t.
Defined.

Definition answer_branch_internal A γ σ γ' (FILTER : filter γ σ γ')
  (br : branch itree γ A) (ans : A) : itree γ' :=
  match br in branch _ _ T return T -> _ with
  | Br_cont cont => br_cont γ σ γ' FILTER cont
  | Br_if con alt => br_if γ σ γ' FILTER con alt
  | Br_dec none add addi ld st beq blt halt =>
    br_dec γ σ γ' FILTER none add addi ld st beq blt halt
  end ans.

Definition answer_branch A γ : branch itree γ A -> A -> itree γ :=
  let (σ, FILTER) := id_filter γ in
  answer_branch_internal A γ σ γ FILTER
.

Compute answer_branch bool [_ ; _]
  (Br_if (Ret (Var (Var_tl Var_hd))) (Call Cycle)) true
.

Definition is_val {A γ} (que : eff γ A) : Prop :=
Eval cbv in ltac:(
  destruct que;
  repeat match goal with
  | v : var _ _ |- _ => exact False
  | v : value _ _ |- _ => destruct v
  end; exact True
).

Definition is_val_dec {A γ} (que : eff γ A) : {is_val que} + {~ is_val que} :=
Eval cbn in ltac:(
  destruct que; cbn;
  repeat match goal with
  | v : value _ _ |- _ => destruct v
  end; solve [right; exact id | left; exact I]
).

Definition destruct_value {Goal γ T} (v : value γ T)
  (var_case : var γ T -> Goal γ T)
  (val_case : T -> Goal γ T)
  : Goal γ T :=
  match v as v'
    return match v' with Var _ => var γ T | Val _ => T end -> Goal γ T
  with
  | Var _ => var_case
  | Val _ => val_case
  end match v with Var x => x | Val v => v end.

Tactic Notation "des_val" ident(v) :=
  eapply (destruct_value v); clear v; intro v
.

Definition destruct_bop {Goal A B C}
  (op : bop A B C) (lop : A) (rop : B)
  (add_case : forall ADD : True, int -> int -> Goal int)
  (eqb_case : forall EQB : True, int -> int -> Goal bool)
  (ltb_case : forall LTB : True, int -> int -> Goal bool)
  : Goal C :=
  match op in bop A' B' C' return True -> A' -> B' -> Goal C' with
  | Bop_add => add_case
  | Bop_eqb => eqb_case
  | Bop_ltb => ltb_case
  end I lop rop.

Tactic Notation "des_bop" ident(op) :=
  eapply (destruct_bop op); eauto; intro
.

Definition test_bop {A γ} (que : eff γ A) : option A.
Proof.
  refine (
  match que with
  | Bop op lop rop => _
  | _ => None
  end).
  des_val lop; [exact None|].
  des_val rop; [exact None|].
  des_bop op.
  - intros x y. exact (Some (x + y)%Z).
  - intros x y. exact (Some (x =? y)%Z).
  - intros x y. exact (Some (x <? y)%Z).
Defined.

Definition test_read_reg {A γ} (que : eff γ A) : option (reg A).
Proof.
  refine (
  match que with
  | Read_reg reg => _
  | _ => None
  end).
  des_val reg; [exact None|].
  exact (Some reg).
Defined.

Definition bop_sem {A B C} (op : bop A B C) : A -> B -> C :=
  match op with
  | Bop_add => Z.add
  | Bop_eqb => Z.eqb
  | Bop_ltb => Z.ltb
  end.

Lemma test_bop_pf γ A B C (op : bop A B C) (lop : A) (rop : B) :
  @test_bop C γ (Bop op (Val lop) (Val rop)) = Some (bop_sem op lop rop).
Proof.
  destruct op; reflexivity.
Qed.

