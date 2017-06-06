Require Import Bool Arith List.
Require Import Coq.Program.Equality.
Require Import Program.
Set Implicit Arguments.
Set Asymmetric Patterns.

Load hlist.
Load ling_syntax.
Load ling_semantics.

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

Eval compute in (expDenote app_prog) HNil.
Eval compute in (expDenote let_ex) HNil.
Eval compute in (expDenote inc) HNil.

(* Transformations *)

Definition Sub G G' := forall t, member t G -> exp G' t. 

Definition idSub {G} : Sub G G := @evar G.

Program Definition consSub {G G' t} (e:exp G' t) (s:Sub G G') : Sub (t::G) G' :=
  fun t' (v: member t' (t::G)) =>
    match v with
    | HFirst _ => e
    | HNext _ _ v' => s _ v'
    end.
    
Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

(* A renaming of environments are where all variables a members of both *)

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

Definition tlSub {G G' t} (s : Sub (t :: G) G') : Sub G G' :=
  fun t' v => s t' (HNext v).

Definition hdSub {G G' t} (s : Sub (t :: G) G') : exp G' t :=
  s t HFirst.

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
  - simpl.
    admit.
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

Lemma capp_total : forall t (v1 v2 : val (TList t)),
    exists v, CApp v1 v2 v.
Proof.
  intros.
  dependent induction v1.
  - exists v2.
    constructor.
  - destruct (IHv1_2 t v1_2) with (v2 := v2).
    reflexivity.
    reflexivity.
    exists (vcons v1_1 x).
    econstructor.
    assumption.
Qed.

Ltac rewriter H :=
  erewrite H; try reflexivity; try eassumption; clear H.
  

(* CApp is deterministic *)
Lemma capp_determ : forall t (v1 v2 v3 v4 : val (TList t)),
    CApp v1 v2 v3 -> CApp v1 v2 v4 -> v3 = v4.
Proof.
  intros t v1 v2 v3 v4 H H'.
  dependent induction H; dependent destruction H'.
  - reflexivity.
  - rewriter IHCApp.
Qed.


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
     (vcons (vconst 11) (vcons (vconst 12) vnil)).
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
      + exists vnil.
        constructor.
      + destruct (IHe1 (HCons x1 R)).
        admit.
    * destruct H0.
      exists x0.
      eapply EvMap.
      eassumption.
      eassumption.
  - destruct (IHe2 R).
    assert (exists v, CFilter R x e1 v).
    * dependent induction x.
      + exists vnil.
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
  - rewriter IHEv1.
    rewriter IHEv2.
  - eapply capp_determ.
    eassumption.
    rewriter IHEv1.
    rewriter IHEv2.
  - apply IHEv in H0.
    apply vconst_congS.
    assumption.
  - rewriter IHEv2.
  - apply IHEv1 in H1.
    inversion H1.
  - apply IHEv in H0_.
    inversion H0_.
  - rewriter IHEv2.
    rewriter IHEv1.
  - rewriter IHEv0.
    rewriter IHEv.
  - rewriter IHEv0.
    rewriter IHEv.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H0.
    rewriter IHEv0.
    rewriter IHEv.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H0.
    rewriter IHEv0.
    apply IHEv in H0.
    inversion H0.
  - dependent destruction H0.
    apply IHEv in H0.
    inversion H0.
    rewriter IHEv0.
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
  intros.
  assert (exists v, Ev R e1 v).
  apply ev_total.
  destruct H0.
  dependent induction x.
  apply EvAndTrue; auto.
  apply EvAndFalse; auto.
Qed.

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
  dependent induction v.


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

Extraction Language Haskell.
Extraction Implicit compose [G].
Recursive Extraction map_fusion.