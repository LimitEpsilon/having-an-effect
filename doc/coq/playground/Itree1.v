From Coq Require Import ZArith List.
From Playground Require Import Var Map.
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

Section Reg.
  (* add here *)
  Universe reg_u.
  Variant reg : Type -> Type@{reg_u} :=
  | Rzero : reg int (* always zero *)
  | Rint (r : int) : reg int
  .

  Definition eqb_reg {A B} (r : reg A) (r' : reg B) : bool :=
  match r with
  | Rzero => match r' with Rzero => true | _ => false end
  | Rint int => match r' with Rint int' => eqb_int int int' | _ => false end
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
  | Inst_ld (rd : reg int) (imm : int) (rs1 : reg int)
  (* ld rd imm(rs1) *)
  (* rd ← M[(rs1) + imm] *)
  | Inst_st (imm : int) (rs1 : reg int) (rs2 : reg int)
  (* st imm(rs1) rs2 *)
  (* M[(rs1) + imm] ← (rs2) *)
  | Inst_beq (rs1 : reg int) (rs2 : reg int) (imm : int)
  (* beq rs1 rs2 imm *)
  (* (pc') = if (rs1) = (rs2) then (pc) + imm else (pc) + 1 *)
  | Inst_blt (rs1 : reg int) (rs2 : reg int) (imm : int)
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
      eqb_reg rd rd' && eqb_reg rs1 rs1' && eqb_int imm imm'
    | _ => false
    end
  | Inst_ld rd imm rs1 =>
    match i' with
    | Inst_ld rd' imm' rs1' =>
      eqb_reg rd rd' && eqb_int imm imm' && eqb_reg rs1 rs1'
    | _ => false
    end
  | Inst_st imm rs1 rs2 =>
    match i' with
    | Inst_st imm' rs1' rs2' =>
      eqb_int imm imm' && eqb_reg rs1 rs1' && eqb_reg rs2 rs2'
    | _ => false
    end
  | Inst_beq rs1 rs2 imm =>
    match i' with
    | Inst_beq rs1' rs2' imm' =>
      eqb_reg rs1 rs1' && eqb_reg rs2 rs2' && eqb_int imm imm'
    | _ => false
    end
  | Inst_blt rs1 rs2 imm =>
    match i' with
    | Inst_blt rs1' rs2' imm' =>
      eqb_reg rs1 rs1' && eqb_reg rs2 rs2' && eqb_int imm imm'
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
  Variant fn {γ : tyenv} : Type@{fn_u} :=
  | Cycle (tgt : value γ int)
  .
End Fn.
Arguments fn : clear implicits.

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
  | Read_mem {A} (addr : value γ int) (mem : mem A) : eff A
  | Read_reg {A} (reg : value γ (reg A)) : eff A
  | Write_mem {A} (addr : value γ int) (mem : mem A) (data : value γ A) : eff unit
  | Write_reg {A} (reg : value γ (reg A)) (data : value γ A) : eff unit
  | Bop {A B C} (op : bop A B C) (lop : value γ A) (rop : value γ B) : eff C
  | Vote (tgt : value γ int) : eff unit
  | Decode (tgt : value γ int) : eff (option inst)
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
    (ld : itree (reg int :: int :: reg int :: γ))
    (st : itree (reg int :: reg int :: int :: γ))
    (beq : itree (int :: reg int :: reg int :: γ))
    (blt : itree (int :: reg int :: reg int :: γ))
    (halt : itree γ)
    : branch (option inst)
  .
End Branch.
Arguments branch : clear implicits.

Section Itree.
  (** γ : the context, not yet determined *)
  Universe itree_u.
Fixpoint args (γ' γ : tyenv) : Type :=
  match γ' with
  | [] => unit
  | A :: tl => (value (A :: γ) A * args tl (A :: γ))%type
  end.

Definition cover {P} A :=
  list {γ & (A -> unit + {σ & filter γ σ []}) * P γ}%type
.

Definition covers {P} A (branch : @cover P A) :=
  forall (x : A),
    let fix go (br : cover A) :=
      match br with
      | [] => False
      | existT _ γ (pat, _) :: tl =>
        match pat x with
        | inl _ => go tl
        | inr _ => True
        end
      end
    in
    go branch.

Inductive itree {eff : tyenv -> Type -> Type} {γ : tyenv} : Type@{itree_u} :=
  | Halt
  | Vis {A}
    (e : eff γ A)
    (k : cover (P := fun γ' => @itree eff (γ' ++ γ)) A)
.

Fixpoint itree_wf {eff γ} (t : itree (eff := eff) (γ := γ)) :=
  match t with
  | Halt => True
  | @Vis _ _ A e k =>
    covers A k /\
    let f br acc :=
      match br with
      | existT _ _ (_, child) => itree_wf child /\ acc
      end
    in
    List.fold_right f True k
  end.

Definition x : itree (eff := fun _ _ => nat) (γ := []) :=
  Vis (A:=unit) 1
  [existT _
    [nat : Type; nat : Type]
    (fun _ => inl tt, Halt)
  ].
End Itree.
Arguments itree : clear implicits.

Unset Printing Universes.

