From Coq Require Import ZArith List.
From Playground Require Import Var.
Import ListNotations.
(* change ITrees to Inductive, and try again? *)
Set Primitive Projections.
Set Printing Universes.

Section Int.
  Universe int_u.
  Definition int : Type@{int_u} := Z.
  Definition eqb_int := Z.eqb.
End Int.

Section Bool.
  Universe bool_u.
  Definition bool : Type@{bool_u} := bool.
End Bool.

Section Addr.
  Universe addr_u.
  Definition addr : Type@{addr_u} := Z.
  Definition eqb_addr := Z.eqb.
End Addr.

Section Reg.
  (* add here *)
  Universe reg_u.
  Variant reg : Type -> Type@{reg_u} :=
  | PC : reg addr
  | Rzero : reg int (* always zero *)
  | Rint (addr : addr) : reg int
  .

  Definition eqb_reg {A B} (r : reg A) (r' : reg B) : bool :=
  match r with
  | PC => match r' with PC => true | _ => false end
  | Rzero => match r' with Rzero => true | _ => false end
  | Rint addr => match r' with Rint addr' => eqb_addr addr addr' | _ => false end
  end.
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

  Definition eqb_inst (i i' : inst) :=
  match i with
  | Inst_add rd rs1 rs2 =>
    match i' with
    | Inst_add rd' rs1' rs2' =>
      eqb_reg rd rd' && eqb_reg rs1 rs1' && eqb_reg rs2 rs2'
    | _ => false
    end
  | Inst_addi rd rs1 imm =>
    match i' with
    | Inst_addi rd' rs1' imm' =>
      eqb_reg rd rd' && eqb_reg rs1 rs1' && eqb_addr imm imm'
    | _ => false
    end
  | Inst_ld rd imm rs1 =>
    match i' with
    | Inst_ld rd' imm' rs1' =>
      eqb_reg rd rd' && eqb_addr imm imm' && eqb_reg rs1 rs1'
    | _ => false
    end
  | Inst_st imm rs1 rs2 =>
    match i' with
    | Inst_st imm' rs1' rs2' =>
      eqb_addr imm imm' && eqb_reg rs1 rs1' && eqb_reg rs2 rs2'
    | _ => false
    end
  | Inst_beq rs1 rs2 imm =>
    match i' with
    | Inst_beq rs1' rs2' imm' =>
      eqb_reg rs1 rs1' && eqb_reg rs2 rs2' && eqb_addr imm imm'
    | _ => false
    end
  | Inst_blt rs1 rs2 imm =>
    match i' with
    | Inst_blt rs1' rs2' imm' =>
      eqb_reg rs1 rs1' && eqb_reg rs2 rs2' && eqb_addr imm imm'
    | _ => false
    end
  | Inst_halt =>
    match i' with
    | Inst_halt => true
    | _ => false
    end
  end%bool.
End Inst.

Section Mem.
  Universe mem_u.
  Variant mem : Type -> Type@{mem_u} :=
  | Imem : mem inst
  | Dmem : mem int
  .

  Definition eqb_mem {A B} (m : mem A) (m' : mem B) : bool :=
  match m with
  | Imem => match m' with Imem => true | _ => false end
  | Dmem => match m' with Dmem => true | _ => false end
  end.
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
  | Halt : itree
  | Call (f : fn) : itree
  | Unanswered {A} (que : eff γ A) (k : @branch (@itree) γ A) : itree
  (*| Answered {A} (que : eff γ A) (ans : A) (k : itree) (rollback : @branch (@itree) γ A) : itree*)
  .
End Itree.
Arguments itree : clear implicits.

Unset Printing Universes.

Notation "'∃?' A x" := (existT option A x)
  (at level 10, A at next level, x at next level).

Definition lift_eff Γ {A γ} (que : eff γ A) : eff (γ ++ Γ) A.
Proof.
  destruct que;
  repeat match goal with
  | v : value ?γ _ |- _ =>
    lazymatch γ with
    | _ ++ _ => fail
    | _ => apply (lift_value Γ) in v
    end
  end.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto.
Defined.

Definition lift_branch Γ {A γ}
  (lift_itree : forall {γ}, itree γ -> itree (γ ++ Γ))
  (br : branch itree γ A) : branch itree (γ ++ Γ) A :=
  match br with
  | Br_cont cont => Br_cont (lift_itree cont)
  | Br_if con alt => Br_if (lift_itree con) (lift_itree alt)
  | Br_dec none add addi ld st beq blt halt =>
    Br_dec
      (lift_itree none)
      (lift_itree add)
      (lift_itree addi)
      (lift_itree ld)
      (lift_itree st)
      (lift_itree beq)
      (lift_itree blt)
      (lift_itree halt)
  end.

Definition lift_itree Γ : forall {γ}, itree γ -> itree (γ ++ Γ) :=
  fix go {γ} t :=
  match t with
  | Halt => Halt
  | Call f => Call f
  | Unanswered que k => Unanswered (lift_eff Γ que) (lift_branch Γ (@go) k)
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

Definition assign_branch
  (assign_itree : forall γ σ γ', filter γ σ γ' -> itree γ -> itree γ')
  {A} γ σ γ'
  (FILTER : filter γ σ γ') (br : branch itree γ A) : branch itree γ' A.
Proof.
  refine (
  match br in branch _ _ A return branch _ _ A with
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
  end);
  repeat econstructor; eauto.
Defined.

Definition assign_itree
  : forall γ σ γ', filter γ σ γ' -> itree γ -> itree γ' :=
  fix go γ σ γ' FILTER t :=
  match t with
  | Halt => Halt
  | Call f => Call f
  | Unanswered que k =>
    Unanswered
      (assign_eff γ σ γ' FILTER que)
      (assign_branch go γ σ γ' FILTER k)
  end.

Definition answer_br_cont {A} γ σ γ' (FILTER : filter γ σ γ')
  (cont : itree (A :: γ))
  : A -> itree γ'.
Proof.
  refine (fun ans =>
  assign_itree (_ :: γ) (∃? _ (Some ans) :: σ) γ' _ cont);
  repeat econstructor; eauto.
Defined.

Definition answer_br_if γ σ γ' (FILTER : filter γ σ γ')
  (con : itree γ)
  (alt : itree γ)
  : bool -> itree γ'.
Proof.
  refine (fun ans =>
  if ans
  then assign_itree γ σ γ' _ con
  else assign_itree γ σ γ' _ alt);
  repeat econstructor; eauto.
Defined.

Definition answer_br_dec γ σ γ' (FILTER : filter γ σ γ')
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
  end);
  repeat econstructor; eauto.
Defined.

Definition answer_branch_internal A γ σ γ' (FILTER : filter γ σ γ')
  (br : branch itree γ A) (ans : A) : itree γ' :=
  match br in branch _ _ A return A -> _ with
  | Br_cont cont => answer_br_cont γ σ γ' FILTER cont
  | Br_if con alt => answer_br_if γ σ γ' FILTER con alt
  | Br_dec none add addi ld st beq blt halt =>
    answer_br_dec γ σ γ' FILTER none add addi ld st beq blt halt
  end ans.

Definition answer_branch A γ : branch itree γ A -> A -> itree γ :=
  let (σ, FILTER) := id_filter γ in
  answer_branch_internal A γ σ γ FILTER
.

Variant answer {h_ty A} :=
  | Ans_done (a : A)
  | Ans_calc (comp : itree []) (upd : h_ty -> h_ty * A)
.

Arguments answer : clear implicits.

Record handler := mkHandler
  {
    h_ty : Type;
    h_state : h_ty;
    h_step : forall A, eff [] A -> option (itree [] * (h_ty -> h_ty * A));
    h_ans : option {A & eff [] A * answer h_ty A}%type;
  }.

Definition destruct_value {A γ} G (v : value γ A)
  : forall
      (var_case : forall x : var γ A, G (Var x))
      (val_case : forall v : A, G (Val v)), G v :=
  match v in (value _ T)
    return
      forall P
        (var_case : forall x : var γ T, P (Var x))
        (val_case : forall v : T, P (Val v)),
        P v
  with
  | Var x => fun _ var_case val_case => var_case x
  | Val v => fun _ var_case val_case => val_case v
  end G.

Tactic Notation "des_val" hyp(v) :=
  revert v;
  match goal with
  | |- forall x, @?P x =>
    intro v;
    simple apply (destruct_value P v);
    clear v; intro v
  end.

Definition to_val {A γ} (que : eff γ A) : option (eff [] A).
Proof.
  destruct que;
  repeat match goal with
  | v : var _ _ |- _ => exact None
  | v : value _ _ |- _ => des_val v
  end; simple apply Some.
  - econstructor 1; try simple apply Val; eauto.
  - econstructor 2; try simple apply Val; eauto.
  - econstructor 3; try simple apply Val; eauto.
  - econstructor 4; try simple apply Val; eauto.
  - econstructor 5; try simple apply Val; eauto.
  - econstructor 6; try simple apply Val; eauto.
  - econstructor 7; try simple apply Val; eauto.
Defined.

Definition from_val {A γ} (que : eff [] A) : eff γ A.
Proof.
  destruct que;
  repeat match goal with
  | v : var _ _ |- _ => eapply empty_var; solve [eauto]
  | v : value _ _ |- _ => des_val v
  end.
  - econstructor 1; try simple apply Val; eauto.
  - econstructor 2; try simple apply Val; eauto.
  - econstructor 3; try simple apply Val; eauto.
  - econstructor 4; try simple apply Val; eauto.
  - econstructor 5; try simple apply Val; eauto.
  - econstructor 6; try simple apply Val; eauto.
  - econstructor 7; try simple apply Val; eauto.
Defined.

Lemma from_to {A γ} (que : eff [] A)
  : (to_val (@from_val _ γ que)) = Some que.
Proof.
  destruct que;
  repeat match goal with
  | v : var _ _ |- _ => eapply empty_var; solve [eauto]
  | v : value _ _ |- _ => des_val v
  end; try reflexivity.
Qed.

Lemma to_from {A γ} (que : eff γ A) que' (TO : to_val que = Some que')
  : from_val que' = que.
Proof.
  destruct que; revert TO;
  repeat match goal with
  | v : value _ _ |- _ =>
    des_val v;
    try solve [intro; inversion TO; subst; auto]
  end.
Qed.

Definition answer_read_mem {A B}
  (m : mem A) (m' : mem B) addr addr' (ans : B) : option A :=
  match m in mem A return option A with
  | Imem =>
    match m' in mem B return B -> _ with
    | Imem => fun ans' =>
      if eqb_addr addr addr' then Some ans' else None
    | _ => fun _ => None
    end ans
  | Dmem =>
    match m' in mem B return B -> _ with
    | Dmem => fun ans' =>
      if eqb_addr addr addr' then Some ans' else None
    | _ => fun _ => None
    end ans
  end.

Definition answer_read_reg {A B}
  (r : reg A) (r' : reg B) (ans : B) : option A :=
  match r in reg A return option A with
  | PC =>
    match r' in reg A' return A' -> _ with
    | PC => fun ans' => Some ans'
    | _ => fun _ => None
    end ans
  | Rzero =>
    match r' in reg A' return A' -> _ with
    | Rzero => fun ans' => Some ans'
    | _ => fun _ => None
    end ans
  | Rint addr =>
    match r' in reg A' return A' -> _ with
    | Rint addr' => fun ans' =>
      if eqb_addr addr addr' then Some ans' else None
    | _ => fun _ => None
    end ans
  end.

Definition answer_write_mem {A B}
  (m : mem A) (m' : mem B) addr addr' (data : A) (data' : B) (ans : unit) : option unit :=
  match m in mem A return A -> _ with
  | Imem => fun data =>
    match m' in mem A' return A' -> _ with
    | Imem => fun data' =>
      if eqb_addr addr addr' && eqb_inst data data'
      then Some ans
      else None
    | _ => fun _ => None
    end data'
  | Dmem => fun data =>
    match m' in mem A' return A' -> _ with
    | Dmem => fun data' =>
      if eqb_addr addr addr' && eqb_int data data'
      then Some ans
      else None
    | _ => fun _ => None
    end data'
  end%bool data.

Definition answer_write_reg {A B}
  (r : reg A) (r' : reg B) (data : A) (data' : B) (ans : unit) : option unit :=
  match r in reg A return A -> _ with
  | PC => fun data =>
    match r' in reg A' return A' -> _ with
    | PC => fun data' =>
      if eqb_int data data'
      then Some ans
      else None
    | _ => fun _ => None
    end data'
  | Rzero => fun data =>
    match r' in reg A' return A' -> _ with
    | Rzero => fun data' =>
      if eqb_int data data'
      then Some ans
      else None
    | _ => fun _ => None
    end data'
  | Rint addr => fun data =>
    match r' in reg A' return A' -> _ with
    | Rint addr' => fun data' =>
      if eqb_addr addr addr' && eqb_int data data'
      then Some ans
      else None
    | _ => fun _ => None
    end data'
  end%bool data.

Definition answer_bop {A B C A' B' C'}
  (op : bop A B C) (op' : bop A' B' C')
  (lop : A) (lop' : A') (rop : B) (rop' : B') (ans : C') : option C :=
  match op in bop A B C return A -> B -> option C with
  | Bop_add => fun lop rop =>
    match op' in bop A' B' C' return A' -> B' -> C' -> _ with
    | Bop_add => fun lop' rop' ans =>
      if eqb_int lop lop' && eqb_int rop rop'
      then Some ans
      else None
    | _ => fun _ _ _ => None
    end lop' rop' ans
  | Bop_eqb => fun lop rop =>
    match op' in bop A' B' C' return A' -> B' -> C' -> _ with
    | Bop_eqb => fun lop' rop' ans =>
      if eqb_int lop lop' && eqb_int rop rop'
      then Some ans
      else None
    | _ => fun _ _ _ => None
    end lop' rop' ans
  | Bop_ltb => fun lop rop =>
    match op' in bop A' B' C' return A' -> B' -> C' -> _ with
    | Bop_ltb => fun lop' rop' ans =>
      if eqb_int lop lop' && eqb_int rop rop'
      then Some ans
      else None
    | _ => fun _ _ _ => None
    end lop' rop' ans
  end%bool lop rop.

Definition answer_vote
  (tgt : addr) (tgt' : addr) (ans : unit) : option unit :=
  if eqb_addr tgt tgt' then Some ans else None
.

Definition answer_decode
  (tgt : addr) (tgt' : addr) (ans : option inst) : option (option inst) :=
  if eqb_addr tgt tgt' then Some ans else None
.

Definition answer_eff {A B} (que : eff [] A) (que' : eff [] B) (ans' : B) : option A.
Proof.
  refine (
  match que in eff _ τ return option τ with
  | Read_mem addr mem =>
    match que' in eff _ τ' return τ' -> option _ with
    | Read_mem addr' mem' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Read_reg reg =>
    match que' in eff _ τ' return τ' -> option _ with
    | Read_reg reg' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Write_mem addr mem data =>
    match que' in eff _ τ' return τ' -> option _ with
    | Write_mem addr' mem' data' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Write_reg reg data =>
    match que' in eff _ τ' return τ' -> option _ with
    | Write_reg reg' data' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Bop op lop rop =>
    match que' in eff _ τ' return τ' -> option _ with
    | Bop op' lop' rop' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Vote tgt =>
    match que' in eff _ τ' return τ' -> option _ with
    | Vote tgt' => fun ans => _
    | _ => fun _ => None
    end ans'
  | Decode tgt =>
    match que' in eff _ τ' return τ' -> option _ with
    | Decode tgt' => fun ans => _
    | _ => fun _ => None
    end ans'
  end);
  repeat match goal with
  | x : var _ _ |- _ => exact (empty_var x)
  | v : value _ _ |- _ => des_val v
  end; clear ans'.
  - exact (answer_read_mem mem mem' addr addr' ans).
  - exact (answer_read_reg reg reg' ans).
  - exact (answer_write_mem mem mem' addr addr' data data' ans).
  - exact (answer_write_reg reg reg' data data' ans).
  - exact (answer_bop op op' lop lop' rop rop' ans).
  - exact (answer_vote tgt tgt' ans).
  - exact (answer_decode tgt tgt' ans).
Defined.

Definition map_branch (f : forall {γ}, itree γ -> itree γ) :=
  fun {A γ} (br : branch itree γ A) =>
    match br in branch _ _ T return branch itree γ T with
    | Br_cont cont => Br_cont (f cont)
    | Br_if con alt => Br_if (f con) (f alt)
    | Br_dec none add addi ld st beq blt halt =>
      Br_dec (f none) (f add) (f addi) (f ld) (f st) (f beq) (f blt) (f halt)
    end.

Definition answer_itree {A γ} (t : itree γ) (que : eff [] A) (ans : A) :=
  let fix go γ (t : itree γ) : itree γ :=
    match t with
    | Halt => Halt
    | Call f => Call f
    | Unanswered que' k =>
      let k' := map_branch go k in
      match to_val que' with
      | None => Unanswered que' k'
      | Some que_v =>
        match answer_eff que_v que ans with
        | None => Unanswered que' k'
        | Some ans' =>
          (* note : answer the topmost node *)
          answer_branch _ γ k ans'
        end
      end
    end
  in
  go γ t.

Inductive system :=
  | Sys_storage (h : handler) (children : list system)
  | Sys_control (comp : itree [])
.

Definition step_system
  (handle_system : _ -> _ -> handler * system)
  : system -> system :=
  fix go sys :=
  match sys with
  | Sys_storage h children =>
    let children' := List.map go children in
    let (h', children'') := List.fold_left
      (fun (acc : handler * list system) child =>
        let (h_acc, rev_children) := acc in
        let (h', child') := handle_system h_acc child in
        (h', child' :: rev_children)) children' (h, [])
    in
    Sys_storage h' (rev children'')
  | Sys_control comp => Sys_control comp
  end.

Definition handle_system
  (handle_itree : _ -> _ -> handler * itree [])
  : handler -> system -> handler * system :=
  fix go h_top sys :=
  match sys with
  | Sys_storage h children =>
    let (h_top', children') := List.fold_left
      (fun (acc : handler * list system) child =>
        let (h_acc, rev_children) := acc in
        let (h', child') := go h_acc child in
        (h', child' :: rev_children)) children (h_top, [])
    in
    let (h_top'', h_ans') :=
      match h.(h_ans) with
      | Some (existT _ τ (que, Ans_calc comp upd)) =>
        let (h_top'', comp') := handle_itree h_top' comp in
        (h_top'', Some (existT _ τ (que, Ans_calc comp' upd)))
      | _ => (h_top', h.(h_ans))
      end
    in
    let h' := {|
      h_ty := h.(h_ty);
      h_state := h.(h_state);
      h_step := h.(h_step);
      h_ans := h_ans'
    |}
    in
    (h_top'', Sys_storage h' (rev children'))
  | Sys_control comp =>
    let (h_top', comp') := handle_itree h_top comp in
    (h_top', Sys_control comp')
  end.

Definition ask_branch {A B γ}
  (ask_itree : forall {γ}, itree γ -> option B) (br : branch itree γ A)
  : option B :=
  match br with
  | Br_cont cont => ask_itree cont
  | Br_if con alt =>
    match ask_itree con with
    | Some res => Some res
    | None => ask_itree alt
    end
  | Br_dec none add addi ld st beq blt halt =>
    match ask_itree none with
    | Some res => Some res
    | None =>
    match ask_itree add with
    | Some res => Some res
    | None =>
    match ask_itree addi with
    | Some res => Some res
    | None =>
    match ask_itree ld with
    | Some res => Some res
    | None =>
    match ask_itree st with
    | Some res => Some res
    | None =>
    match ask_itree beq with
    | Some res => Some res
    | None =>
    match ask_itree blt with
    | Some res => Some res
    | None =>
    match ask_itree halt with
    | Some res => Some res
    | None => None
    end end end end end end end end
  end.

Definition ask_itree {γ h_ty} (t : itree γ)
  (h_step : forall A, eff [] A -> option (itree [] * (h_ty -> h_ty * A)))
  : option {A & eff [] A * answer h_ty A}%type :=
  let fix go γ (t : itree γ) :=
    match t with
    | Halt => None
    | Call f => None
    | @Unanswered _ A que k =>
      match to_val que with
      | None => ask_branch go k
      | Some que' =>
        match h_step _ que' with
        | None => ask_branch go k
        | Some (t, upd) => Some (existT _ A (que', Ans_calc t upd))
        end
      end
    end
  in go γ t.

(* in step: takes questions or answers questions that are computed *)
(* prepare for step:
    clear answered questions or
    compute answer and update state *)
(* the pending question should be represented as:
   1. answered state : answer
   2. preparing state : itree * (state update / answer computing function)
   3. free state : none *)
Definition handle_itree {γ} (h : handler) (t : itree γ) : handler * itree γ :=
  match h.(h_ans) with
  | None =>
    let h' := {|
      h_ty := h.(h_ty);
      h_state := h.(h_state);
      h_step := h.(h_step);
      h_ans := ask_itree t h.(h_step);
    |}
    in
    (h', t)
  | Some (existT _ τ (_, Ans_calc _ _)) => (h, t)
  | Some (existT _ τ (que', Ans_done ans')) => (h, answer_itree t que' ans')
  end.

Definition do_step := step_system (handle_system handle_itree).

Definition prepare_step (call : fn -> itree []) : system -> system :=
  fix go sys :=
  match sys with
  | Sys_storage h children =>
    let (h_state', h_ans') :=
      match h.(h_ans) with
      | Some (existT _ τ (que, Ans_calc comp upd)) =>
        match comp with
        | Halt =>
          let (h_state', a) := upd h.(h_state) in
          (h_state', Some (existT _ τ (que, Ans_done a)))
        | Call f =>
          (h.(h_state), Some (existT _ τ (que, Ans_calc (call f) upd)))
        | _ => (h.(h_state), Some (existT _ τ (que, Ans_calc comp upd)))
        end
      | _ => (h.(h_state), None)
      end
    in
    let h' := {|
      h_ty := h.(h_ty);
      h_state := h_state';
      h_step := h.(h_step);
      h_ans := h_ans';
    |}
    in
    Sys_storage h' (map go children)
  | Sys_control comp =>
    match comp with
    | Call f => Sys_control (call f)
    | _ => Sys_control comp
    end
  end.

Definition step call sys := prepare_step call (do_step sys).

Definition cycle : itree [].
Proof.
  refine (
  Unanswered (Read_reg (Val PC))
    (Br_cont
      (Unanswered (Decode (Var Var_hd))
        (Br_dec
          (Unanswered (Vote (Var Var_hd))
            (Br_cont (Call Cycle))
          )
          _ _ _ _ _ _ _
        )
      )
    )
  ).
  - (* add *) admit.
  - (* addi *) admit.
  - (* ld *) admit.
  - (* st *) admit.
  - (* beq *) admit.
  - (* blt *) admit.
  - (* halt *) admit.
Admitted.
