Definition ty_ctx := list ty.
Definition ev_ctx (G : ty_ctx) := hlist val G.

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

(* Inductive judgment for append *)
Inductive CApp : forall t,
    val (TList t) -> val (TList t) -> val (TList t) -> Prop :=
| CAppNil : forall t (v : val (TList t)), CApp vnil v v
(* Corresponds to the recursive case for append *)
| CAppCons : forall t v (v1 : val t) v2 v3,
    CApp v2 v3 v -> CApp (vcons v1 v2) v3 (vcons v1 v).

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
    Ev R enil (@vnil t)
| EvCons : forall (G : ty_ctx) (R : ev_ctx G)
                  t e1 e2 (v1 : val t) (v2 : val (TList t)),
    Ev R e1 v1 -> Ev R e2 v2 -> Ev R (econs e1 e2) (vcons v1 v2)
(* For append we hand the calculation off to the append rule *)
| EvAppend : forall (G : ty_ctx) (R : ev_ctx G) t
                    (e1 e2 : exp G (TList t)) (v1 v2 : val (TList t)) v,
    Ev R e1 v1 -> Ev R e2 v2 ->
    CApp v1 v2 v -> Ev R (eappend e1 e2) v
| EvSucc : forall (G : ty_ctx) (R : ev_ctx G) e n,
    Ev R e (vconst n) -> Ev R (esucc e) (vconst (S n))
| EvAndTrue : forall (G : ty_ctx) (R : ev_ctx G) e1 e2 (v : val TBool),
    Ev R e1 vtrue -> Ev R e2 v -> Ev R (eand e1 e2) v
(* Short circuiting and *)
| EvAndFalse : forall (G : ty_ctx) (R : ev_ctx G) e1 e2,
    Ev R e1 vfalse -> Ev R (eand e1 e2) vfalse
| EvLet : forall (G : ty_ctx) (R : ev_ctx G)
                 t1 t2 (e1 : exp G t1) (e2 : exp (t1 :: G) t2) v1 (v2 : val t2),
    Ev R e1 v1 -> Ev (HCons v1 R) e2 v2 -> Ev R (elet e1 e2) v2
(* For map we hand off the calculation the the map rule *)
| EvMap : forall (G : ty_ctx) (R : ev_ctx G) t1 t2
                 (e1 : exp (t1 :: G) t2) (e2 : exp G (TList t1)) v v',
                 Ev R e2 v ->
                 CMap R v e1 v' ->
                 Ev R (emap e1 e2) v'
(* For filter we hand off the calculation the the filter rule *)
| EvFilter : forall (G : ty_ctx) (R : ev_ctx G) t
                 (e1 : exp (t :: G) TBool) (e2 : exp G (TList t)) v v',
                 Ev R e2 v ->
                 CFilter R v e1 v' ->
                 Ev R (efilter e1 e2) v'
 with CMap : forall G t1 t2,
    ev_ctx G -> val (TList t1) -> exp (t1 :: G) t2 -> val (TList t2) -> Prop :=
      | CMapNil : forall (G : ty_ctx) (R : ev_ctx G) t1 t2 (e : exp (t1 :: G) t2),
          CMap R vnil e vnil
      | CMapCons : forall (G : ty_ctx) (R : ev_ctx G) t1 t2 (e : exp (t1 :: G) t2)
        v1 v2 v1' v2',
          (* We bind the first element of the list to the evaluation context
             and evaluate the function *)
          Ev (HCons v1 R) e v1' ->
          CMap R v2 e v2' ->
          (* And cons the result back on *)
          CMap R (vcons v1 v2) e (vcons v1' v2')
 with CFilter : forall G t,
     ev_ctx G -> val (TList t) -> exp (t :: G) TBool -> val (TList t) -> Prop :=
      | CFilterNil : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool),
          CFilter R vnil e vnil
      (* We split filter into two cases, one when the function evalutates to true
         and one when the function evaluates to false *)
      | CFilterTrue : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool) v1 v2 v2',
          Ev (HCons v1 R) e vtrue ->
          CFilter R v2 e v2' ->
          CFilter R (vcons v1 v2) e (vcons v1 v2')
      | CFilterFalse : forall (G : ty_ctx) (R : ev_ctx G) t (e : exp (t :: G) TBool) v1 v2 v2',
          Ev (HCons v1 R) e vfalse ->
          CFilter R v2 e v2' ->
          CFilter R (vcons v1 v2) e v2'.

(* Mutual induction principle for Ev *)
Scheme Ev_mut := Induction for Ev Sort Prop
                 with CMap_mut := Induction for CMap Sort Prop
                with CFilter_mut := Induction for CFilter Sort Prop.