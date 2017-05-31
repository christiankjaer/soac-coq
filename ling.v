Require Import Bool Arith List.
Require Import Coq.Program.Equality.
Require Import Program.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Adam Chlipalas heterogeneous list implementation (magic inside)
 * Useful for De Bruijn indices
 *)

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
    | HNil
      => fun mem =>
           match mem in member ls'
                 return (match ls' with
                         | nil => B elm
                         | _ :: _ => unit
                         end) with
           | HFirst _ => tt
           | HNext _ _ _ => tt
           end
    | HCons _ _ x mls'
      => fun mem =>
           match mem in member ls'
                 return (match ls' with
                         | nil => Empty_set
                         | x' :: ls'' =>
                           B x' -> (member ls'' -> B elm)
                           -> B elm
                         end) with
           | HFirst _ => fun x _ => x
           | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
           end x (hget mls')
    end.
  
End hlist.

Arguments HNil [A B].
Arguments HCons [A B x ls].

Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls].

Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

Lemma ty_eq_dec :
  forall t1 t2 : ty, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

Definition env := list ty.

(* Intrinsically typed expression syntax *)
Inductive exp G : ty -> Type :=
| evar : forall t, member t G -> exp G t
| etrue : exp G TBool
| efalse : exp G TBool
| econst : nat -> exp G TNat
| esucc : exp G TNat -> exp G TNat
| eand : exp G TBool -> exp G TBool -> exp G TBool
| enil : forall t, exp G (TList t)
| econs : forall t, exp G t -> exp G (TList t) -> exp G (TList t)
| elet : forall t1 t2, exp G t1 -> exp (t1 :: G) t2 -> exp G t2
| eappend : forall t, exp G (TList t) -> exp G (TList t) -> exp G (TList t)
| emap : forall t1 t2, exp (t1 :: G) t2 -> exp G (TList t1) -> exp G (TList t2)
| efilter : forall t1, exp (t1 :: G) TBool -> exp G (TList t1) -> exp G (TList t1).

Arguments econst [G].
Arguments etrue [G].
Arguments efalse [G].
Arguments enil [G t].

Notation "[| |]" := enil.
Notation "[| x |]" := (econs x enil).
Notation "[| x ; y ; .. ; z |]" := (econs x (econs y .. (econs z enil) ..)).
Notation "[| x ; .. ; y |]" := (econs x .. (econs y enil) ..).

(* Intrinsically typed values as well *)
Inductive val : ty -> Type :=
| vtrue : val TBool
| vfalse : val TBool
| vconst : nat -> val TNat
| vnil : forall t, val (TList t)
| vcons : forall t, val t -> val (TList t) -> val (TList t).

Notation "[|| ||]" := vnil.
Notation "[|| x ||]" := (vcons x vnil).
Notation "[|| x ; y ; .. ; z ||]" := (vcons x (vcons y .. (vcons z vnil) ..)).
Notation "[|| x ; .. ; y ||]" := (vcons x .. (vcons y vnil) ..).

Example inc : exp nil (TList TNat) :=
  emap (esucc (evar HFirst)) (econs (econst 4) (econs (econst 5) enil)).

Check emap (esucc (evar HFirst)) (econs (econst 4) (econs (econst 5) enil)).
Check (evar (HNext HFirst)).

Example let_ex : exp nil TNat :=
  elet (econst 42) (esucc (evar HFirst)).

Example app_prog : exp nil (TList TNat) := eappend (econs (econst 0) enil) (econs (econst 1) enil).

Example nested_map : exp nil (TList TNat) :=
  emap (esucc (evar HFirst))
  (emap (esucc (evar HFirst)) [| econst 1 ; econst 2 ; econst 3 |]).

Example flat_map : exp nil (TList TNat) :=
  emap (esucc (esucc (evar HFirst)))
       [| econst 1 ; econst 2 ; econst 3 |].

Definition Sub G G' := forall t, member t G -> exp G' t. 

Definition idSub {G} : Sub G G := @evar G.

Program Definition consSub {G G' t} (e:exp G' t) (s:Sub G G') : Sub (t::G) G' :=
  fun t' (v: member t' (t::G)) =>
    match v with
    | HFirst _ => e
    | HNext _ _ v' => s _ v'
    end.
    
Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Check @member.

Definition Ren G G' := forall t, @member ty t G -> @member ty t G'.

Program Definition renameLift {G G' t}
        (r : Ren G G') : Ren (t :: G) (t :: G') :=
  fun t' v =>
    match v with
    | HFirst _ => @HFirst ty t _
    | HNext _ _ v' => HNext (r _ v')
    end.

Fixpoint renameExp G G' t (r : Ren G G') (e : exp G t) :=
  match e with
  | evar _ x => evar (r _ x)
  | etrue => etrue
  | efalse => efalse
  | econst n => econst n
  | esucc e => esucc (renameExp r e)
  | eand e1 e2 => eand (renameExp r e1) (renameExp r e2)
  | enil _ => enil
  | econs _ e1 e2 => econs (renameExp r e1) (renameExp r e2)
  | elet _ _ e1 e2 => elet (renameExp r e1) (renameExp (renameLift r) e2)
  | eappend _ e1 e2 => eappend (renameExp r e1) (renameExp r e2)
  | emap _ _ e1 e2 => emap (renameExp (renameLift r) e1) (renameExp r e2)
  | efilter _ e1 e2 => efilter (renameExp (renameLift r) e1) (renameExp r e2)
  end.

Definition shiftExp G t t' : exp G t -> exp (t' :: G) t :=
  renameExp (fun _ v => HNext v).

Definition shift2Exp G t1 t2 t3 : exp (t2 :: G) t3 -> exp (t2 :: t1 :: G) t3.
  refine (renameExp (fun _ v => _)).
  inversion v; subst; repeat constructor; auto.
Defined.

Program Definition
        subShift {G G'} t (s : Sub G G') : Sub (t :: G) (t :: G') :=
  fun t' v =>
    match v with
    | HFirst _ => evar HFirst
    | HNext _ _ v' => shiftExp t (s _ v')
    end.

Fixpoint subExp G G' t (s : Sub G G') (e : exp G t) :=
  match e with
  | evar _ x => s _ x
  | etrue => etrue
  | efalse => efalse
  | econst n => econst n
  | esucc e => esucc (subExp s e)
  | eand e1 e2 => eand (subExp s e1) (subExp s e2)
  | enil _ => enil
  | econs _ e1 e2 => econs (subExp s e1) (subExp s e2)
  | elet _ _ e1 e2 => elet (subExp s e1) (subExp (subShift s) e2)
  | eappend _ e1 e2 => eappend (subExp s e1) (subExp s e2)
  | emap _ _ e1 e2 => emap (subExp (subShift s) e1) (subExp s e2)
  | efilter _ e1 e2 => efilter (subExp (subShift s) e1) (subExp s e2)
  end.

Definition compose t1 t2 t3 G (f : exp (t1 :: G) t2) (g : exp (t2 :: G) t3) : exp (t1 :: G) t3 :=
  subExp {| f |} (shift2Exp _ g).

Fixpoint tyDenote (t : ty) : Type :=
  match t with
  | TBool => bool
  | TNat => nat
  | TList t => list (tyDenote t)
  end.

Fixpoint valDenote t (v : val t) : tyDenote t :=
  match v with
  | vfalse => false
  | vtrue => true
  | vconst n => n
  | vnil _ => nil
  | vcons _ v1 v2 => (valDenote v1) :: (valDenote v2)
  end.

(* An interpreter *)
Fixpoint expDenote G t (e : exp G t) : hlist tyDenote G -> tyDenote t :=
  match e with
  | evar _ x => fun s => hget s x 
  | econst n => fun _ => n
  | etrue => fun _ => true
  | efalse => fun _ => false
  | esucc e => fun s => S (expDenote e s)
  | eand e1 e2 => fun s => (expDenote e1 s) && (expDenote e2 s)
  | enil _ => fun _ => nil
  | econs _ e1 e2 => fun s => (expDenote e1 s) :: (expDenote e2 s)
  | elet _ _ e el =>
    fun s => expDenote el (HCons (expDenote e s) s)
  | eappend _ e1 e2 => fun s => app (expDenote e1 s) (expDenote e2 s)
  | emap _ _ ef e =>
    fun s => let f := fun x => expDenote ef (HCons x s)
             in map f (expDenote e s)
  | efilter _ ef e =>
    fun s => let f := fun x => expDenote ef (HCons x s)
             in filter f (expDenote e s)
  end.

Eval compute in (expDenote app_prog) HNil.
Eval compute in (expDenote let_ex) HNil.
Eval compute in (expDenote inc) HNil.

Lemma map_id : forall G t (e : exp G t) s,
    expDenote (elet e (evar HFirst)) s = expDenote e s.
Proof.
  intros. simpl. reflexivity.
Qed.
  
Lemma append_assoc : forall G t (e1 e2 e3: exp G (TList t)) s,
    expDenote (eappend (eappend e1 e2) e3) s =
    expDenote (eappend e1 (eappend e2 e3)) s.
Proof.
  intros.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Definition tlSub {G G' t} (s : Sub (t :: G) G') : Sub G G' :=
  fun t' v => s t' (HNext v).

Definition hdSub {G G' t} (s : Sub (t :: G) G') : exp G' t :=
  s t HFirst.

Definition ty_ctx := list ty.
Definition ev_ctx G := hlist val G.

Eval compute in compose (econst 10) (elet (econst 10) (evar (HFirst))).

Definition filter_fusion t G (e : exp G t) : exp G t.
  refine
    (match e in exp _ t' return exp G t' -> exp G t' with
     | efilter te p em => (fun lt (em' : exp G lt) =>
                             match em' in exp _ lt return (TList te = lt -> _) with
                             | efilter t' q eb => fun Heq _ => efilter (eand _ q) eb
                             | _ => fun _ e => e
                             end) (TList te) em _
     | _ => fun e => e
     end e).
  injection Heq. intros. rewrite <- H. exact p.
  trivial.
Defined.

Definition map_fusion t G (e : exp G t) : exp G t.
  refine (match e in exp _ t' return exp G t' -> exp G t' with
          | emap t2 t3 g em => (fun lt2 (em' : exp G lt2) =>
                                  match em' in exp _ lt2 return (TList t2 = lt2 -> _) with
                                  | emap t3 t2' f eb => fun Heq _ => emap (compose f _) eb
                                  | _ => fun _ e => e
                                  end) (TList t2) em _
          |  _ => fun e => e
          end e).
  injection Heq. intros. subst. exact g.
  trivial.
Defined.

Extraction filter_fusion.


Lemma compose_sound : forall t1 t2 t3 G R (f : exp (t1 :: G) t2) (g : exp (t2 :: G) t3) v1,
    expDenote g (HCons (expDenote f (HCons v1 R)) R) =
    expDenote (compose f g) (HCons v1 R).
Proof.
  intros.
  generalize dependent f.
  generalize dependent v1.
  dependent induction g; intros; try reflexivity.
  - dependent destruction m; try reflexivity.
  - simpl. rewrite IHg; try reflexivity.
  - simpl.
    rewrite IHg1; try reflexivity.
    rewrite IHg2; try reflexivity.
  - simpl.
    rewrite IHg1; try reflexivity.
    rewrite IHg2; try reflexivity.
  - admit. (* let case *)
  - simpl.
    rewrite IHg1; try reflexivity.
    rewrite IHg2; try reflexivity.
  - admit. (* map case *)
  - admit. (* filter case *)
Admitted.
  
Theorem map_fusion_sound t (e : exp nil t) s : expDenote e s = expDenote (map_fusion e) s.
Proof.
  (* Eliminate all the trivial cases *)
  dependent destruction e; 
    try (simpl; reflexivity).
  dependent destruction e2;
    try (simpl; reflexivity).
  simpl.
  (* Now do induction over what the list evaluates to *)
  induction (expDenote e2_2 s).
  - reflexivity.
  - simpl.
    rewrite compose_sound.
    rewrite IHt.
    reflexivity.
Qed.

Theorem filter_fusion_sound t (e : exp nil t) s : expDenote e s = expDenote (filter_fusion e) s.
  Proof.
    (* Eliminate all the trivial cases *)
    dependent destruction e; 
      try (simpl; reflexivity).
    dependent destruction e2;
      try (simpl; reflexivity).
    simpl.
    (* Now do induction over what the list evaluates to *)
    induction (expDenote e2_2 s).
    - reflexivity.
    - simpl.
      destruct (expDenote e2_1 (HCons a s)); simpl.
      destruct (expDenote e1 (HCons a s)); simpl;
        try rewrite <- IHt;
        reflexivity.
      rewrite -> andb_b_false.
      rewrite <- IHt.
      reflexivity.
Qed.

(* Inductive judgment for append *)
Inductive CApp : forall t,
    val (TList t) -> val (TList t) -> val (TList t) -> Prop :=
| CAppNil : forall t (v : val (TList t)), CApp (vnil t) v v
| CAppCons : forall t v (v1 : val t) v2 v3,
    CApp v2 v3 v -> CApp (vcons v1 v2) v3 (vcons v1 v).


Lemma capp_total : forall t (v1 v2 : val (TList t)),
    exists v, CApp v1 v2 v.
Proof.
  intros.
  dependent induction v1.
  exists v2.
  constructor.
  destruct (IHv1_2 t v1_2) with (v2 := v2).
  reflexivity.
  reflexivity.
  exists (vcons v1_1 x).
  econstructor.
  assumption.
Qed.

(* CApp is deterministic *)
Lemma capp_determ : forall t (v1 v2 v3 v4 : val (TList t)),
    CApp v1 v2 v3 -> CApp v1 v2 v4 -> v3 = v4.
Proof.
  intros t v1 v2 v3 v4 H H'.
  dependent induction H; dependent destruction H'.
  - reflexivity.
  - rewrite (IHCApp v0). reflexivity. assumption.
Qed.

Inductive Ev : forall G t, ev_ctx G -> exp G t -> val t -> Prop :=
| EvVar : forall G R t (m : member t G),
    Ev R (evar m) (hget R m)
| EvTrue : forall (G : ty_ctx) (R : ev_ctx G),
    Ev R etrue vtrue
| EvFalse : forall (G : ty_ctx) (R : ev_ctx G),
    Ev R efalse vfalse
| EvConst : forall (G : ty_ctx) (R : ev_ctx G) n,
    Ev R (econst n) (vconst n)
| EvNil : forall (G : ty_ctx) (R : ev_ctx G) t,
    Ev R enil (vnil t)
| EvCons : forall (G : ty_ctx) (R : ev_ctx G)
                  t e1 e2 (v1 : val t) (v2 : val (TList t)),
    Ev R e1 v1 -> Ev R e2 v2 -> Ev R (econs e1 e2) (vcons v1 v2)
| EvAppend : forall (G : ty_ctx) (R : ev_ctx G) t
                    (e1 e2 : exp G (TList t)) (v1 v2 : val (TList t)) v,
    Ev R e1 v1 -> Ev R e2 v2 ->
    CApp v1 v2 v -> Ev R (eappend e1 e2) v
| EvSucc : forall (G : ty_ctx) (R : ev_ctx G) e n,
    Ev R e (vconst n) -> Ev R (esucc e) (vconst (S n))
| EvAndTrue : forall (G : ty_ctx) (R : ev_ctx G) e1 e2 (v : val TBool),
    Ev R e1 vtrue -> Ev R e2 v -> Ev R (eand e1 e2) v
| EvAndFalse : forall (G : ty_ctx) (R : ev_ctx G) e1 e2,
    Ev R e1 vfalse -> Ev R (eand e1 e2) vfalse
| EvLet : forall (G : ty_ctx) (R : ev_ctx G)
                 t1 t2 (e1 : exp G t1) (e2 : exp (t1 :: G) t2) v1 (v2 : val t2),
    Ev R e1 v1 -> Ev (HCons v1 R) e2 v2 -> Ev R (elet e1 e2) v2
| EvMap : forall (G : ty_ctx) (R : ev_ctx G) t1 t2
                 (e1 : exp (t1 :: G) t2) (e2 : exp G (TList t1)) v v',
                 Ev R e2 v ->
                 CMap R v e1 v' ->
                 Ev R (emap e1 e2) v'
| EvFilter : forall (G : ty_ctx) (R : ev_ctx G) t
                 (e1 : exp (t :: G) TBool) (e2 : exp G (TList t)) v v',
                 Ev R e2 v ->
                 CFilter R v e1 v' ->
                 Ev R (efilter e1 e2) v'
 with CMap : forall G t1 t2,
    ev_ctx G -> val (TList t1) -> exp (t1 :: G) t2 -> val (TList t2) -> Prop :=
      | CMapNil : forall (G : ty_ctx) (R : ev_ctx G) t1 t2 (e : exp (t1 :: G) t2),
          CMap R (vnil t1) e (vnil t2)
      | CMapCons : forall (G : ty_ctx) (R : ev_ctx G) t1 t2 (e : exp (t1 :: G) t2)
        v1 v2 v1' v2',
          Ev (HCons v1 R) e v1' ->
          CMap R v2 e v2' ->
          CMap R (vcons v1 v2) e (vcons v1' v2')
 with CFilter : forall G t,
     ev_ctx G -> val (TList t) -> exp (t :: G) TBool -> val (TList t) -> Prop :=
      | CFilterNil : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool),
          CFilter R (vnil t) e (vnil t)
      | CFilterTrue : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool) v1 v2 v2',
          Ev (HCons v1 R) e vtrue ->
          CFilter R v2 e v2' ->
          CFilter R (vcons v1 v2) e (vcons v1 v2')
      | CFilterFalse : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool) v1 v2 v2',
          Ev (HCons v1 R) e vfalse ->
          CFilter R v2 e v2' ->
          CFilter R (vcons v1 v2) e v2'.

Scheme Ev_mut := Induction for Ev Sort Prop
                 with CMap_mut := Induction for CMap Sort Prop
                                  with CFilter_mut := Induction for CFilter Sort Prop.

Check Ev_mut.

Example ev_example :
  Ev (HCons (vconst 1) HNil) (evar HFirst) (vconst 1).
apply EvVar.
Qed.

Example ev_let :
  Ev HNil (elet (econst 10) (esucc (evar HFirst))) (vconst 11).
repeat econstructor.
Qed.

Example ev_map :
  Ev HNil (emap (esucc (evar HFirst)) [| econst 10 ; econst 11 |])
     (vcons (vconst 11) (vcons (vconst 12) (vnil TNat))).
repeat econstructor.
Qed.

Lemma vconst_congS : forall n n0, vconst n = vconst n0 -> vconst (S n) = vconst (S n0).
Proof.
  intros.
  congruence.
Qed.


Theorem ev_total : forall G t (R : ev_ctx G) (e : exp G t),
    exists v, Ev R e v.
Proof.
  intros.
  dependent induction e.
  - (eexists; constructor).
  - (eexists; constructor).
  - (eexists; constructor).
  - (eexists; constructor).
  - destruct (IHe R).
    dependent destruction x.
    exists (vconst (S n)).
    constructor.
    assumption.
  - destruct (IHe1 R).
    destruct (IHe2 R).
    dependent destruction x;
      dependent destruction x0.
    exists vtrue.
    constructor.
    assumption.
    assumption.
    exists vfalse.
    constructor.
    assumption.
    assumption.
    exists vfalse.
    apply EvAndFalse.
    assumption.
    exists vfalse.
    apply EvAndFalse.
    assumption.
  - (eexists; constructor).
  - destruct (IHe1 R).
    destruct (IHe2 R).
    exists (vcons x x0).
    constructor.
    assumption.
    assumption.
  - destruct (IHe1 R).
    destruct (IHe2 (HCons x R)).
    exists x0.
    eapply EvLet.
    eassumption.
    assumption.
  - destruct (IHe1 R).
    destruct (IHe2 R).
    assert (exists v, CApp x x0 v).
    apply capp_total with (v1 := x) (v2 := x0).
    destruct H1.
    exists x1.
    eapply EvAppend.
    eassumption.
    eassumption.
    assumption.
  - destruct (IHe2 R).
    assert (exists v, CMap R x e1 v).
    * dependent induction x.
      + exists (vnil t2).
        constructor.
      + admit.
    * destruct H0.
      exists x0.
      eapply EvMap.
      eassumption.
      eassumption.
  - destruct (IHe2 R).
    assert (exists v, CFilter R x e1 v).
    * dependent induction x.
      + exists (vnil t1).
        constructor.
      + admit.
    * destruct H0.
        exists x0.
        eapply EvFilter.
        eassumption.
        eassumption.
Admitted.

Ltac ev_destructor :=
  match goal with
  | [ H : Ev _ _ ?v |- _ = ?v ] => dependent destruction H; try reflexivity
  end.
  
Theorem ev_determ : forall G t (R : ev_ctx G) (e: exp G t) v1 v2,
      Ev R e v1 -> Ev R e v2 -> v1 = v2.
Proof.
  intros.
  generalize dependent v2.
  induction H using Ev_mut with
      (P := fun (G : list ty) (t : ty) (R : ev_ctx G) (e : exp G t) (v : val t) (ev : Ev R e v) => forall v2, Ev R e v2 -> v = v2)
      (P0 := fun (G : list ty) (t1 t2 : ty) (R : ev_ctx G) 
                 (v : val (TList t1)) (e : exp (t1 :: G) t2) (v0 : val (TList t2))
                 (ev : CMap R v e v0) => forall v2, CMap R v e v2 -> v0 = v2)
      (P1 := fun (G : list ty) (t : ty) (R : ev_ctx G) 
                 (v : val (TList t)) (e : exp (t :: G) TBool) (v0 : val (TList t))
                 (ev : CFilter R v e v0) => forall v2, CFilter R v e v2 -> v0 = v2);
    intros; try ev_destructor.
  erewrite IHEv1.
  erewrite IHEv2.
  reflexivity.
  assumption.
  assumption.
  eapply capp_determ.
  eassumption.
  erewrite IHEv1.
  erewrite IHEv2.
  eassumption.
  assumption.
  assumption.
  apply IHEv in H0.
  apply vconst_congS.
  assumption.
  apply (IHEv2 v2).
  assumption.
  apply IHEv1 in H1.
  inversion H1.
  apply IHEv in H0_.
  inversion H0_.
  apply (IHEv2 v3).
  rewrite (IHEv1 v0).
  assumption.
  assumption.
  rewrite (IHEv0 v2).
  reflexivity.
  rewrite (IHEv v0).
  assumption.
  assumption.
  rewrite (IHEv0 v2).
  reflexivity.
  rewrite (IHEv v0).
  assumption.
  assumption.
  dependent destruction H.
  reflexivity.
  dependent destruction H0.
  rewrite (IHEv0 v2'0).
  rewrite (IHEv v1'0).
  reflexivity.
  assumption.
  assumption.
  dependent destruction H.
  reflexivity.
  dependent destruction H0.
  rewrite (IHEv0 v2'0).
  reflexivity.
  assumption.
  apply IHEv in H0.
  inversion H0.
  dependent destruction H0.
  apply IHEv in H0.
  inversion H0.
  rewrite (IHEv0 v2'0).
  reflexivity.
  assumption.
Qed.

Lemma let_id_sound2 : forall t G (R : ev_ctx G) (e : exp G t) (v1 v2 : val t),
    Ev R e v1 -> Ev R (elet e (evar HFirst)) v2 -> v1 = v2.
Proof. intros.
       apply EvLet with (e2 := (evar HFirst)) (v2 := v1) in H.
       apply (ev_determ H) in H0.
       exact H0. constructor. Qed.
  

Lemma and_r_false : forall G (R : ev_ctx G) (e1 e2 : exp G TBool),
    Ev R e2 vfalse -> Ev R (eand e1 e2) vfalse.
Proof.
Admitted.

Theorem filter_fusion_sound2 : forall t G (R : ev_ctx G) (e : exp G t) (v : val t),
        Ev R e v -> Ev R (filter_fusion e) v.
Proof.
  intros.
  dependent destruction e;
    try (unfold filter_fusion;
         assumption).
  dependent destruction e2;
    try (unfold filter_fusion;
         assumption).
  simpl.
  dependent destruction H.
  dependent destruction H.
  econstructor.
  exact H.
  dependent induction v1.
  dependent destruction H0.
  dependent destruction H1.
  constructor.
  dependent destruction v.
  dependent destruction v0.
  dependent destruction H0.
  eapply CFilterFalse.
  apply and_r_false.
Admitted.


Theorem map_fusion_sound2 : forall t G (R : ev_ctx G) (e : exp G t) (v : val t),
        Ev R e v -> Ev R (map_fusion e) v.
Proof.
  intros.
  dependent destruction e;
  try (unfold map_fusion in *;
       assumption).
  dependent destruction e2;
  try (unfold map_fusion in *;
       assumption).

Admitted.
