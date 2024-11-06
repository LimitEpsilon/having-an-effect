From Coq Require Import PArith.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Inductive ptree' {V} :=
  | PNodeM (l : option ptree') (v : V) (r : option ptree')
  | PNode0 (l : ptree') (r : option ptree')
  | PNode1 (r : ptree')
.

Arguments ptree' : clear implicits.

(* smart constructor *)
Definition pnode {V : Type} l (v : option V) r :=
  match l, v, r with
  | _, Some v', _ => Some (PNodeM l v' r)
  | Some l', _, _ => Some (PNode0 l' r)
  | _, _, Some r' => Some (PNode1 r')
  | _, _, _ => None
  end.

Definition palter {V : Type} (f : option V -> option V) :=
  Eval cbv in
  fix alter (i : positive) (m : option (ptree' V)) :=
  match i with
  | 1 =>
    match m with
    | None => pnode None (f None) None
    | Some (PNodeM l v r) => pnode l (f (Some v)) r
    | Some (PNode0 l r) => pnode (Some l) (f None) r
    | Some (PNode1 r) => pnode None (f None) (Some r)
    end
  | p~0 =>
    match m with
    | None => pnode (alter p None) None None
    | Some (PNodeM l v r) => pnode (alter p l) (Some v) r
    | Some (PNode0 l r) => pnode (alter p (Some l)) None r
    | Some (PNode1 r) => pnode (alter p None) None (Some r)
    end
  | p~1 =>
    match m with
    | None => pnode None None (alter p None)
    | Some (PNodeM l v r) => pnode l (Some v) (alter p r)
    | Some (PNode0 l r) => pnode (Some l) None (alter p r)
    | Some (PNode1 r) => pnode None None (alter p (Some r))
    end
  end%positive.

Definition pfind' {A B : Type} (f : A -> B) :=
  fix find' (i : positive) (m' : ptree' A) :=
  let find i m := match m with None => None | Some m' => find' i m' end
  in match i with
  | 1 =>
    match m' with
    | PNodeM _ v _ => Some (f v)
    | _ => None
    end
  | p~0 =>
    match m' with
    | PNodeM l _ _ => find p l
    | PNode0 l _ => find' p l
    | _ => None
    end
  | p~1 =>
    match m' with
    | PNodeM _ _ r | PNode0 _ r=> find p r
    | PNode1 r => find' p r
    end
  end%positive.

Definition pfmap' {A B} (f : A -> B) :=
  fix fmap' (m' : ptree' A) :=
  let fmap m := match m with None => None | Some m' => Some (fmap' m') end
  in match m' with
  | PNodeM l v r => PNodeM (fmap l) (f v) (fmap r)
  | PNode0 l r => PNode0 (fmap' l) (fmap r)
  | PNode1 r => PNode1 (fmap' r)
  end.

Definition pomap' {A B} (f : A -> option B) :=
  Eval cbv in
  fix omap' (m' : ptree' A) :=
  let omap m := match m with None => None | Some m' => omap' m' end
  in match m' with
  | PNodeM l v r => pnode (omap l) (f v) (omap r)
  | PNode0 l r => pnode (omap' l) None (omap r)
  | PNode1 r => pnode None None (omap' r)
  end.

Definition pfold' {R K V : Type} (f : R -> K -> V -> R) :=
  fix fold' (acc' : R) k' (m' : ptree' V) : R :=
  let foldl acc k l := fold' acc (fun x => k (x~0))%positive l in
  let foldr acc k r := fold' acc (fun x => k (x~1))%positive r in
  match m' with
  | PNodeM l v r =>
    let accl := match l with None => acc' | Some l' => foldl acc' k' l' end in
    let accv := f accl (k' 1) v in
    let accr := match r with None => accv | Some r' => foldr accv k' r' end in
    accr
  | PNode0 l r =>
    let accl := foldl acc' k' l in
    let accr := match r with None => accl | Some r' => foldr accl k' r' end in
    accr
  | PNode1 r =>
    let accr := foldr acc' k' r in
    accr
  end%positive.

Record map V :=
  {
    nmap : option (ptree' V);
    zmap : option V;
    pmap : option (ptree' V)
  }.

Definition empty {V} : map V :=
  {| nmap := None; zmap := None; pmap := None |}
.

Definition read {V} (k : Z) (m : map V) : option V :=
  match k with
  | Zneg p =>
    match m.(nmap) with
    | None => None
    | Some t => pfind' id p t
    end
  | Z0 => m.(zmap)
  | Zpos p =>
    match m.(pmap) with
    | None => None
    | Some t => pfind' id p t
    end
  end.

Definition update {V} (k : Z) (v : V) (m : map V) : map V :=
  let nmap := m.(nmap) in
  let zmap := m.(zmap) in
  let pmap := m.(pmap) in
  let upd (_ : option V) := Some v in
  match k with
  | Zneg p =>
    {|
      nmap := palter upd p nmap;
      zmap := zmap;
      pmap := pmap;
    |}
  | Z0 =>
    {|
      nmap := nmap;
      zmap := Some v;
      pmap := pmap;
    |}
  | Zpos p =>
    {|
      nmap := nmap;
      zmap := zmap;
      pmap := palter upd p pmap;
    |}
  end.

Module LMap.
Inductive tm :=
  | Var (x : positive)
  | Lam (x : positive) (e : tm)
  | App (f a : tm)
.

Scheme tm_ind := Induction for tm Sort Prop.

(* flat term *)
Inductive tmF : nat -> Type :=
  | TmF : tmF O
  | VarF n (x : positive) (k : tmF n) : tmF (S n)
  | LamF n (x : positive) (k : tmF (S n)) : tmF (S n)
  | AppF n (k : tmF (S (S n))) : tmF (S n)
.

Scheme tmF_ind := Induction for tmF Sort Prop.

Inductive tmList : nat -> Type :=
  | TmNil : tmList O
  | TmCons n (hd : tm) (tl : tmList n) : tmList (S n)
.

Fixpoint tmCons (t : tm) n (k : tmF n) : tmF (S n) :=
  match t with
  | Var x => VarF x k
  | Lam x e => LamF x (tmCons e k)
  | App e1 e2 => AppF (tmCons e1 (tmCons e2 k))
  end.

Definition tmHd {n} (l : tmList (S n)) : tm :=
  match l in tmList m return match m with O => unit | S _ => tm end with
  | TmNil => tt
  | TmCons hd _ => hd
  end.

Definition tmTl {n} (l : tmList (S n)) : tmList n :=
  match l in tmList m return match m with O => unit | S m' => tmList m' end with
  | TmNil => tt
  | TmCons _ tl => tl
  end.

Definition tmList_des {n} (l : tmList n) :
  match n return tmList n -> Prop with
  | O => fun l => l = TmNil
  | S n' => fun l => l = TmCons (tmHd l) (tmTl l)
  end l.
Proof. destruct l; auto. Qed.

Tactic Notation "unfold_tmlist" constr(l) := rewrite (tmList_des l).
Tactic Notation "unfold_tmlist" constr(l) "in" constr(H) := rewrite (tmList_des l) in H.
Tactic Notation "unfold_tmlist" constr(l) "in" "*" := rewrite (tmList_des l) in *.

Fixpoint tmF_to_tmList n (t : tmF n) : tmList n.
Proof.
  destruct t.
  - exact TmNil.
  - exact (TmCons (Var x) (tmF_to_tmList _ t)).
  - apply tmF_to_tmList in t.
    set (e := tmHd t).
    exact (TmCons (Lam x e) (tmTl t)).
  - apply tmF_to_tmList in t.
    set (e1 := tmHd t).
    set (e2 := tmHd (tmTl t)).
    exact (TmCons (App e1 e2) (tmTl (tmTl t))).
Defined.

Fixpoint tmList_to_tmF n (l : tmList n) : tmF n.
Proof.
  destruct l.
  - exact TmF.
  - exact (tmCons hd (tmList_to_tmF _ l)).
Defined.

Definition tm_to_tmF t := tmCons t TmF.
Definition tmF_to_tm (t' : tmF 1) := tmHd (tmF_to_tmList t').

Lemma tmCons_TmCons (t : tm) :
  forall n (t' : tmF n),
    tmF_to_tmList (tmCons t t') = TmCons t (tmF_to_tmList t').
Proof.
  induction t; intros; cbn; auto.
  - rewrite IHt. auto.
  - rewrite IHt1, IHt2. auto.
Qed.

Lemma tmF_to_tmList_to_tmF n (l : tmList n) :
  tmF_to_tmList (tmList_to_tmF l) = l.
Proof.
  induction n; unfold_tmlist l.
  - auto.
  - simpl. rewrite tmCons_TmCons. rewrite IHn. auto.
Qed.

Lemma tmList_to_tmF_to_tmList n (t : tmF n) :
  tmList_to_tmF (tmF_to_tmList t) = t.
Proof.
  induction t; simpl; auto.
  - rewrite IHt. auto.
  - unfold_tmlist (tmF_to_tmList t) in IHt.
    f_equal. auto.
  - unfold_tmlist (tmF_to_tmList t) in IHt.
    unfold_tmlist (tmTl (tmF_to_tmList t)) in IHt.
    f_equal. auto.
Qed.

Lemma tmF_to_tm_to_tmF (t : tm) :
  tmF_to_tm (tm_to_tmF t) = t.
Proof.
  unfold tmF_to_tm, tm_to_tmF.
  rewrite tmCons_TmCons. auto.
Qed.

Lemma tm_to_tmF_to_tm (t : tmF 1) :
  tm_to_tmF (tmF_to_tm t) = t.
Proof.
  unfold tm_to_tmF, tmF_to_tm.
  pose proof (tmList_to_tmF_to_tmList t) as PF.
  unfold_tmlist (tmF_to_tmList t) in PF.
  unfold_tmlist (tmTl (tmF_to_tmList t)) in PF.
  assumption.
Qed.

Inductive tmtree' {V : Type} : nat -> Type :=
  | TmLeaf (v : V) : tmtree' O
  | TmNodeV n
    (x : ptree' (tmtree' n))
    (l : option (ptree' (tmtree' (S n))))
    (a : option (tmtree' (S (S n))))
  : tmtree' (S n)
  | TmNodeL n
    (l : ptree' (tmtree' (S n)))
    (a : option (tmtree' (S (S n))))
  : tmtree' (S n)
  | TmNodeA n
    (a : tmtree' (S (S n)))
  : tmtree' (S n)
.

Arguments tmtree' : clear implicits.

Definition tmfold' {R K V} (f : R -> K -> V -> R) :
  forall (n : nat), R -> (tmF n -> K) -> (tmtree' V n) -> R.
Proof.
  refine (fix fold' n (acc' : R) k' (m' : tmtree' V n) {struct m'} : R := _).
  set (foldx n acc k x := pfold' (fold' n) acc (fun x t => k (VarF x t)) x).
  set (foldl n acc k l := pfold' (fold' (S n)) acc (fun x t => k (LamF x t)) l).
  set (folda n acc k a := fold' (S (S n)) acc (fun t => k (AppF t)) a).
  destruct m'.
  - exact (f acc' (k' TmF) v).
  - set (accx := foldx n acc' k' x).
    set (accl := match l with None => accx | Some l' => foldl n accx k' l' end).
    set (acca := match a with None => accl | Some a' => folda n accl k' a' end).
    exact acca.
  - set (accl := foldl n acc' k' l).
    set (acca := match a with None => accl | Some a' => folda n accl k' a' end).
    exact acca.
  - set (acca := folda n acc' k' m').
    exact acca.
Defined.
End LMap.

