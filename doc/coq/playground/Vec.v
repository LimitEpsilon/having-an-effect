From Coq Require Import Arith.
Local Unset Elimination Schemes.

(* length-indexed list *)
Inductive vec {A : Type} : nat -> Type :=
  | vnil : vec 0
  | vcons {n} (hd : A) (tl : vec n) : vec (S n)
.

Section VEC_IND.
  Context {A : Type}.
  Context (P : forall n, @vec A n -> Prop).
  Context (Pnil : P 0 vnil)
          (Pcons : forall n hd tl (IHtl : P n tl), P (S n) (vcons hd tl)).

  Fixpoint vec_ind {n} (v : @vec A n) : P n v :=
    match v as v' in vec n' return P n' v' with
    | vnil => Pnil
    | @vcons _ n' hd tl => Pcons n' hd tl (vec_ind tl)
    end.
End VEC_IND.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Infix "::" := vcons.
Notation "[ ]" := vnil (format "[ ]") : vec_scope.
Notation "[ x ]" := (vcons x vnil) : vec_scope.
Notation "[ x ; y ; .. ; z ]" := (vcons x (vcons y .. (vcons z vnil) ..)) : vec_scope.

Arguments vec : clear implicits.

Fixpoint get_idx {A n} (l : vec A n) (i : nat) (pf : S i <= n) : A.
Proof.
  refine (
    match l in vec _ n' return S i <= n' -> A with
    | [] => _
    | hd :: tl => _
    end%vec pf
  ); intro LE.
  - exfalso.
    eapply Nat.nle_succ_0; eauto.
  - destruct i.
    + exact hd.
    + refine (get_idx A _ tl i _).
      apply le_S_n; assumption.
Defined.

Definition fold_vec {A B} (f : A -> B -> A) :=
  fix fold {n} (l : vec B n) (acc : A) {struct l} : A :=
    match l with
    | [] => acc
    | hd :: tl => fold tl (f acc hd)
    end%vec.

Definition map_vec {A B} (f : A -> B) :=
  fix map {n} (l : vec A n) {struct l} : vec B n :=
    match l with
    | [] => []
    | hd :: tl => (f hd) :: (map tl)
    end%vec.

Definition In_vec {A} (x : A) :=
  fix In {n} (l : vec A n) {struct l} : Prop :=
    match l with
    | [] => False
    | hd :: tl => x = hd \/ In tl
    end%vec.

Fixpoint map_vec_In {A B n} (l : vec A n) (f : forall x, In_vec x l -> B) {struct l} : vec B n.
Proof.
  destruct l.
  - exact vnil.
  - apply vcons.
    + eapply (f hd _).
    + eapply (map_vec_In _ _ _ l _).
      Unshelve.
      simpl. left; reflexivity.
      intros. eapply f. simpl. eauto.
Defined.

