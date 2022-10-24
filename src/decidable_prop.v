Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Bool.
Require Import Morphisms List list_tools.

(** * Decidable sets *)

(** The class of [decidable_set X] contains a binary function associating to every pair of elements of type [X] a boolean and a proof that this function encodes faithfully equality over [X]. *)
Class decidable_set X :=
  { eqX : X -> X -> bool;
    eqX_eq : forall x y, reflect (x = y) (eqX x y)}.

Infix " =?= " := eqX (at level 20).

Section decidable.
  Context { X : Set }.
  Context { D : decidable_set X }.
 
  (** This lemma is the preferred way of translating back and forth between boolean and propositional equality. *)
  Lemma eqX_correct : forall x y : X, eqX x y = true <-> x = y.
  Proof. intros;symmetry;apply reflect_iff,eqX_eq. Qed.

  (** The next few lemmas are useful on occasion.  *)
  Lemma eqX_false : forall x y, eqX x y = false <-> x <> y.
  Proof. intros;rewrite<-(eqX_correct _),not_true_iff_false;tauto. Qed.

  Lemma X_dec (x y : X) : {x = y} + {x <> y}.
  Proof.
    case_eq (eqX x y).
    - now intro h;left;apply (eqX_correct _).
    - intro h;right;intro E;apply (eqX_correct _) in E.
      contradict E;rewrite h;auto.
  Qed.

  Lemma eqX_refl x : eqX x x = true.
  Proof. apply eqX_correct;reflexivity. Qed.

End decidable.

(* begin hide *)
Ltac destruct_eqX x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ _ x o) as [Ei |Ni];
  [pose proof Ei as X;apply (@eqX_correct _ _) in X;
   try rewrite Ei in *
  |pose proof Ni as X;apply (@eqX_false _ _) in X];
  repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X.

Ltac simpl_beq :=
  match goal with
  | [h: ?a <> ?b |- _] =>
    let E := fresh "E" in
    pose h as E;apply eqX_false in E;rewrite E in *;clear E
  | [h: ?a <> ?b |- _] =>
    let E := fresh "E" in
    assert (E:b<>a) by (intros E;apply h;rewrite E;reflexivity);
    apply eqX_false in E;rewrite E in *;clear E
  | _ => rewrite eqX_refl in *
  end.
Ltac simpl_eqX :=
  repeat
    simpl_beq
  || match goal with
    | [ |- context[?x =?= ?o]] =>
      let Ei := fresh "E" in
      let Ni := fresh "N" in
      let X := fresh "X" in
      destruct (@X_dec _ _ x o) as [Ei |Ni];
      [pose proof Ei as X;apply (@eqX_correct _ _) in X;
       try rewrite Ei in *;tauto||discriminate
      |pose proof Ni as X;apply (@eqX_false _ _) in X];
      repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X
    end.
Ltac unfold_eqX :=
  repeat
    simpl_beq
  || match goal with
    | [ |- context[?x =?= ?o]] =>
      let Ei := fresh "E" in
      let Ni := fresh "N" in
      let X := fresh "X" in
      destruct (@X_dec _ _ x o) as [Ei |Ni];
      [pose proof Ei as X;apply (@eqX_correct _ _) in X;
       try rewrite Ei in *
      |pose proof Ni as X;apply (@eqX_false _ _) in X];
      repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X
    end.
(* end hide *)
  
(** The set of natural numbers is decidable. *)
Global Instance NatNum : decidable_set nat :=
  Build_decidable_set PeanoNat.Nat.eqb_spec.


(** The set of natural booleans is decidable. *)
Global Instance Boolean : decidable_set bool.
Proof.
  cut (forall x y, reflect (x = y) (eqb x y));
  [apply Build_decidable_set|].
  intros;apply iff_reflect;symmetry;apply eqb_true_iff.
Qed.

(** If [A] and [B] are decidable, then so is their Cartesian product. *)
Global Instance dec_prod A B :
  decidable_set A -> decidable_set B -> decidable_set (A*B).
Proof.
  intros d1 d2.
  set (eqp := fun x y =>
                (@eqX _ d1 (fst x) (fst y))
                  && (@eqX _ d2 (snd x) (snd y))).
  assert (eqp_spec : forall x y, reflect (x=y) (eqp x y));
    [|apply (Build_decidable_set eqp_spec)].
  intros (x1,x2) (y1,y2);unfold eqp;simpl;
  destruct (@eqX_eq _ d1 x1 y1);destruct (@eqX_eq _ d2 x2 y2);
  apply ReflectT||apply ReflectF;
  (rewrite e,e0;reflexivity)||(intro h;inversion h;tauto).
Qed.

(** If [A] and [B] are decidable, then so is their sum. *)
Global Instance dec_sum A B :
  decidable_set A -> decidable_set B -> decidable_set (A+B).
Proof.
  intros d1 d2.
  set (eqp := fun (x y : A+B) =>
                match (x,y) with
                | (inl _,inr _) | (inr _,inl _) => false
                | (inl a,inl b) => a =?= b
                | (inr a,inr b) => a =?= b
                end).
  assert (eqp_spec : forall x y, reflect (x=y) (eqp x y));
    [|apply (Build_decidable_set eqp_spec)].
  intros [x|x] [y|y];unfold eqp;simpl.
  - destruct (@eqX_eq _ d1 x y).
    + apply ReflectT;subst;auto.
    + apply ReflectF;intro h;inversion h;tauto.
  - apply ReflectF;discriminate.
  - apply ReflectF;discriminate.
  - destruct (@eqX_eq _ d2 x y).
    + apply ReflectT;subst;auto.
    + apply ReflectF;intro h;inversion h;tauto.
Qed.

(** If [A] is decidable, then so is [option A]. *)
Global Instance dec_option (A : Set) :
  decidable_set A -> decidable_set (option A).
Proof.
  intros d1.
  set (eqlbl :=
         fun l1 l2 : option A =>
           match (l1,l2) with
           | (None,None) => true
           | (Some x,Some y) => eqX x y
           | _ => false
           end).
  exists eqlbl;intros [|] [|];apply iff_reflect;unfold eqlbl;simpl;split;
    try discriminate || tauto.
  * intros E;inversion E; apply eqX_refl.
  * rewrite eqX_correct;intros ->;reflexivity.
Qed.


Class DecidableProp (P : Prop) := dec_prop: {P} + {~ P}.
Arguments dec_prop : clear implicits.
Arguments dec_prop P {DecidableProp}.

Ltac case_prop p :=
  let D := fresh "D" in
  let hyp := fresh "hyp" in
  destruct (dec_prop p) as [hyp|hyp].

Global Instance DecidableProp_Eq (A : Set) (x y : A) :
  decidable_set A -> DecidableProp (x=y).
Proof. intro;destruct_eqX x y;[left;reflexivity|right;assumption]. Qed.

Definition test (p : Prop) {d : DecidableProp p} : bool :=
  if (dec_prop p) then true else false.

Arguments test p {d}.

Lemma test_reflect p `{DecidableProp p} : reflect p (test p).
Proof. unfold test;case_prop p;[apply ReflectT|apply ReflectF];assumption. Qed.

Remark Is_true_test p `{DecidableProp p} : Is_true (test p) <-> p.
Proof.
  split;intro h.
  - rewrite reflect_iff by apply test_reflect;apply Is_true_eq_true,h.
  - apply Is_true_eq_left;rewrite <-reflect_iff by apply test_reflect;assumption.
Qed.
Global Instance Is_true_dec b : DecidableProp (Is_true b).
Proof. destruct b;[left|right];simpl;auto. Qed.
Remark Is_true_iff_eq_true b : Is_true b <-> b = true.
Proof. destruct b;simpl;[tauto|split;[tauto|discriminate]]. Qed.
Remark test_Is_true (p : bool) : test (Is_true p) = p.
Proof.
  apply eq_iff_eq_true;rewrite <- reflect_iff by apply test_reflect.
  apply Is_true_iff_eq_true.
Qed.
Remark test_spec ϕ `{DecidableProp ϕ} : test ϕ = true <-> ϕ.
Proof. rewrite <-reflect_iff by apply test_reflect;reflexivity. Qed.

Global Instance DecidableProp_neg p : DecidableProp p -> DecidableProp (~p).
Proof. intro D;case_prop p;[right|left];tauto. Qed.
  
Global Instance DecidableProp_conj p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 /\ p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||(right;tauto). Qed.

Global Instance DecidableProp_disj p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 \/ p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||(right;tauto). Qed.

Global Instance DecidableProp_impl p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 -> p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||right;tauto. Qed.

Global Instance DecidableProp_iff p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 <-> p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||right;tauto. Qed.

Global Instance DecidableProp_forall_bnd (A : Set) p l :
  (forall a : A, DecidableProp (p a)) -> 
  DecidableProp (forall a, a ∈ l -> p a).
Proof.
  intros dp.
  case_eq (forallb (fun a => test (p a)) l);intro E;[left|right].
  - rewrite forallb_forall in E.
    intros a Ia.
    apply E in Ia.
    rewrite reflect_iff by apply test_reflect.
    assumption.
  - apply forallb_false_exists in E as (a&Ia&Fa).
    intros h;apply h in Ia.
    rewrite reflect_iff in Ia by apply test_reflect.
    rewrite Ia in Fa;discriminate.
Qed.

Global Instance DecidableProp_exists_bnd (A : Set) p l :
  (forall a : A, DecidableProp (p a)) -> DecidableProp (exists a, a ∈ l /\ p a).
Proof.
  intros dp.
  case_eq (existsb (fun a => test (p a)) l);intro E;[left|right].
  - apply existsb_exists in E as (a&Ia&Pa).
    rewrite <- reflect_iff in Pa by apply test_reflect.
    exists a;tauto.
  - intros (a&Ia&Pa);apply not_true_iff_false in E;apply E,existsb_exists.
    exists a;split;[assumption|].
    rewrite <- reflect_iff by apply test_reflect.
    assumption.
Qed.

Global Instance DecidableProp_equiv_prop p q :
  DecidableProp p -> (p <-> q) -> DecidableProp q.
Proof. intros D E;case_prop p;[left|right];rewrite <- E;assumption. Qed.

Ltac prove_proper :=
  match goal with
  | _ : _ |- Proper ((@equivalent _) ==> iff) _ =>
    let l := fresh "l" in
    let m := fresh "m" in
    let E := fresh "E" in
    intros l m E;setoid_rewrite E;reflexivity
  end.

(* Tactics *)

Lemma andb_prop_iff x y: Is_true (x && y) <-> Is_true x /\ Is_true y.
Proof.
  split; [apply andb_prop_elim | apply andb_prop_intro].
Qed.

Lemma orb_prop_iff x y: Is_true (x || y) <-> Is_true x \/ Is_true y.
Proof.
  split; [apply orb_prop_elim | apply orb_prop_intro].
Qed.

Global Hint Rewrite andb_prop_iff orb_prop_iff : quotebool.

Ltac case_equal a b :=
  let E := fresh "E" in
  destruct (X_dec a b) as [E|E];
    [try rewrite E in *|].
Goal (forall n, n = 0 \/ n <> 0).
Proof. intro n;case_equal n 0;tauto. Qed.

Ltac mega_simpl :=
  repeat (simpl in *;
           rewrite in_app_iff
           || match goal with
              | [ h : In _ (map _ _ ) |- _ ] => 
                let u1 := fresh "u" in
                apply in_map_iff in h as (u1&<-&h)
              | [ h : _ \/ _ |- _ ] =>
                destruct h as [h|h]
              | [ h : In _ (_ ++ _ ) |- _ ] =>
                apply in_app_iff in h as [h|h]
              | [ _ : False |- _ ] => tauto
              | |- (forall _, _) => intro
              | |- (_ -> _) => intro
              | |- (In _ (map _ _)) => apply in_map_iff
              | |- (In _ (_ ++ _)) => apply in_app_iff
              | |- (_ /\ _) => split
              | |- (_ \/ False) => left
              | |- (exists _, _) => eexists
              | [ h : In _ ?l |- In _ ?l ] => apply h
              | [ h : In _ ?l |- In _ ?l \/ _ ] => left;apply h
              | [ h : In _ ?l |- _ \/ In _ ?l ] => right;apply h
              end).



Ltac destruct_eqb x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (PeanoNat.Nat.eq_dec x o) as [Ei |Ni];
    [pose proof Ei as X;apply PeanoNat.Nat.eqb_eq in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply PeanoNat.Nat.eqb_neq in X];
    try rewrite X in *;clear X;
    repeat  (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).
Ltac destruct_eqX_D D x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ D x o) as [Ei |Ni];
    [pose proof Ei as X;apply (@eqX_correct _ D)in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply  (@eqX_false _ D) in X];
    repeat rewrite X in *;repeat rewrite (eqX_refl D) in *;clear X.
Ltac destruct_ltb x o :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [pose proof Li as X;apply PeanoNat.Nat.ltb_ge in X
    |pose proof Li as X;apply PeanoNat.Nat.ltb_lt in X];
    try rewrite X in *;clear X;
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac destruct_leb o x :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [try rewrite (Compare_dec.leb_correct _ _ Li) in *
    |try rewrite (Compare_dec.leb_correct_conv _ _ Li) in *];
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac simpl_words :=
  try discriminate;
  match goal with
  | [h: [] = _ ++ _ :: _ |- _ ] => apply app_cons_not_nil in h;tauto
  | [h: _ ++ _ :: _ = [] |- _ ] => symmetry in h;apply app_cons_not_nil in h;tauto
  | [h: _ ++ [_] = _ ++ [_] |- _ ] =>
    let h' := fresh "h" in
    apply app_inj_tail in h as (h,h');
    try discriminate
  end.

   (* end hide *)
