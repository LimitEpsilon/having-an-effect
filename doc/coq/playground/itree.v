From Coq Require Import ZArith List.
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
  | Filter_cons_some A a γ σ γ'
    (FILTER : filter γ σ γ')
    : filter (A :: γ) (existT option A (Some a) :: σ) γ'
  | Filter_cons_none A γ σ γ'
    (FILTER : filter γ σ γ')
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

Section Eff.
  (* add here *)
  Universe eff_u.
  Variant eff {γ : tyenv} : Type -> Type@{eff_u} :=
  | Read_mem {A} (addr : value γ addr) (mem : mem A) : eff A
  | Read_reg {A} (reg : value γ (reg A)) : eff A
  | Write_mem {A} (addr : value γ addr) (mem : mem A) (data : A) : eff unit
  | Write_reg {A} (reg : value γ (reg A)) (data : value γ A) : eff A
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

Definition shift_value {γ A} B (v : value γ A) : value (B :: γ) A.
Proof.
  destruct v.
  - destruct γ as [|τ τl].
    + exact (empty_var x).
    + refine (match x in var (τ' :: τl') A with
      | @Var_hd τl' τ' => _
      | @Var_tl τl' T' τ' x' => _
      end).
      * exact (Var (Var_tl Var_hd)).
      * exact (Var (Var_tl (Var_tl x'))).
  - exact (Val v).
Defined.

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

Fixpoint id_filter γ : {σ & filter γ σ γ} :=
  match γ with
  | [] => existT (fun σ => filter [] σ []) [] Filter_nil
  | τ :: τl =>
    let σ := id_filter τl in
    let (tl, FILTER) := σ in
    existT (fun σ => filter (τ :: τl) σ (τ :: τl))
      (existT option τ None :: tl)
      (Filter_cons_none τ τl tl τl FILTER)
  end.

Definition assign_value {A} γ σ γ'
  (FILTER : filter γ σ γ') (v : value γ A) : value γ' A :=
  match v with
  | @Var _ τ x => assign_var γ σ γ' FILTER x
  | @Val _ τ v' => Val v'
  end.

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

