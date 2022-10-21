Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop Psatz.
Require Export list_tools.

(** * Lists over a decidable set *)
Section dec_list.
  Context { A : Set } { dec_A : decidable_set A }.

  (** Boolean equality for lists *)
  Fixpoint equal_list l m :=
    match (l,m) with
    | ([],[]) => true
    | (a::l,b::m) => eqX a b && equal_list l m
    | _ => false
    end.

  Lemma equal_list_spec l m : reflect (l = m) (equal_list l m).
  Proof.
    apply iff_reflect;revert m;induction l as [|a l];intros [|b m];
    simpl;split;try reflexivity||discriminate;
    rewrite andb_true_iff,<-IHl.
    - intro h;inversion h;split;auto;apply eqX_refl.
    - intros (h&->);apply eqX_correct in h as ->;reflexivity.
  Qed.
                                
  (** The set of lists of [A]s is decidable. *)
  Global Instance dec_list : decidable_set (list A).
  Proof. apply (Build_decidable_set equal_list_spec). Qed.

  (** Boolean predicate testing whether an element belongs to a list. *)
  Definition inb (n : A) l := existsb (eqX n) l.
  
  Lemma inb_spec n l : inb n l = true <-> n ∈ l.
  Proof.
    case_eq (inb n l);intro E;unfold inb in *.
    - apply existsb_exists in E as (y&I&E).
      apply eqX_correct in E as ->;tauto.
    - rewrite <- not_true_iff_false, existsb_exists in E;split.
      -- discriminate.
      -- intro I;exfalso;apply E;eexists;split;[eauto|];apply eqX_refl.
  Qed.

  Lemma inb_false n l : inb n l = false <-> ~ n ∈ l.
  Proof. rewrite <- inb_spec,not_true_iff_false;reflexivity. Qed.

  (** This boolean predicate allows us to use the excluded middle with the predicate [In]. *)
  Lemma inb_dec n l : { inb n l = true /\ n ∈ l } + { inb n l = false /\ ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec;auto.
    split;auto;rewrite E;discriminate.
  Qed.

  Lemma In_dec (n : A) l : { n ∈ l } + { ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec,E;auto.
  Qed.
  (* begin hide *)
  Ltac case_in a l :=
    let I := fresh "I" in
    let E := fresh "E" in
    destruct (inb_dec a l) as [(E&I)|(E&I)];
    try rewrite E in *;clear E.
  (* end hide *)

  (** Boolean function implementing containment test. *)  
  Definition inclb (a b : list A) :=
    forallb (fun x => inb x b) a.
  
  Lemma inclb_correct a b : inclb a b = true <-> a ⊆ b.
  Proof.
    unfold incl,inclb;rewrite forallb_forall.
    setoid_rewrite inb_spec;intuition.
  Qed.

  (** Boolean function testing for equivalence of lists. *)
  Definition equivalentb l1 l2 := inclb l1 l2 && inclb l2 l1.

  Lemma equivalentb_spec l1 l2 : equivalentb l1 l2 = true <-> l1 ≈ l2.
  Proof.
    unfold equivalentb;rewrite andb_true_iff,inclb_correct,inclb_correct.
    split.
    - intros (e1&e2);apply incl_PartialOrder;split;tauto.
    - intros ->;split;reflexivity.
  Qed.


  (** If [u=u1++a::u2], we call the triple [(u1,u2)] an [a]-decomposition of [u] if [a] does not appear in [u1]. *)

  (** If [a] is in [l], then there exists an [a]-decomposition of [l]. *)
  Lemma decomposition (a : A) l :
    a ∈ l <-> exists l1 l2, l = l1 ++ a :: l2 /\ ~ a ∈ l1.
  Proof.
    induction l as [|b l];simpl;auto.
    - split;try tauto.
      intros (?&?&?&_).
      apply app_cons_not_nil in H;tauto.
    - destruct_eqX a b.
      + split;auto.
        intros _;exists [],l;split;auto.
      + rewrite IHl;clear IHl;split.
        * intros [<-|(l1&l2&->&h)];[tauto|].
          exists (b::l1),l2;split;auto.
          intros [->|I];tauto.
        * intros (l1&l2&E&I);right.
          destruct l1 as [|c l1].
          -- simpl in *;inversion E;subst;tauto.
          -- simpl in E;inversion E;subst;clear E.
             exists l1,l2;split;auto.
             intro;apply I;now right.
  Qed.

  (** Decompositions are unique.*)
  Lemma decomp_unique (a:A) u1 u2 v1 v2 :
    u1++(a::u2) = v1++a::v2 -> ~ In a v1 -> ~ In a u1 -> u1 = v1 /\ u2 = v2.
  Proof.
    intros E I1 I2;destruct (Levi_strict E) as [(->&E2)|(c&w&[(->&E2)|(->&E2)])];
      inversion E2;subst;clear E2;auto.
    - exfalso;apply I2,in_app_iff;right;left;auto.
    - exfalso;apply I1,in_app_iff;right;left;auto.
  Qed.

  Lemma decomp_unambiguous (u1 u2 v1 v2 : list A) a b :
    u1++a::u2 = v1++b::v2 -> ~ In a v1 -> ~ In b u1 -> u1 = v1 /\ a=b /\ u2 = v2.
  Proof.
    intros E Ia Ib;destruct (Levi_strict E) as [(->&E2)|(c&w&[(->&E2)|(->&E2)])].
    - inversion E2;auto.
    - exfalso;apply Ib;rewrite in_app_iff;simpl.
      inversion E2;auto.
    - exfalso;apply Ia;rewrite in_app_iff;simpl.
      inversion E2;auto.
  Qed.

  (** [{{l}}] is a list containing the same elements as [l], but without duplication. *)
  Definition undup l :=
    fold_right (fun a acc =>
                  if inb a acc
                  then acc
                  else a::acc)
               nil
               l.

  Notation " {{ l }} " := (undup l) (at level 0).

  (** [{{l}}] is shorter than [l]. *)
  Lemma undup_length l : ⎢{{l}}⎥ <= ⎢l⎥ .
  Proof. induction l;rsimpl; [|destruct (inb a _);rsimpl];lia. Qed.

  (** [{{l}}] contains the same elements as [l]. *)
  Lemma In_undup a l: a ∈ {{l}} <-> a ∈ l.
  Proof.
    revert a; induction l;simpl;auto;try tauto.
    intro b;case_in a {{l}};simpl;rewrite IHl in *;try tauto.
    destruct_eqX a b;tauto.
  Qed.
  (*begin hide *)
  Ltac simpl_In :=
    repeat rewrite in_app_iff
    || rewrite <- In_rev
    || rewrite In_undup
    || rewrite filter_In.
  Tactic Notation "simpl_In" "in" hyp(h) :=
    repeat rewrite in_app_iff in h
    || rewrite <- In_rev in h
    || rewrite In_undup in h
    || rewrite filter_In in h.
  Tactic Notation "simpl_In" "in" "*" :=
    repeat rewrite in_app_iff in *
    || rewrite <- In_rev in *
    || rewrite In_undup in *
    || rewrite filter_In in *.
  (* end hide *)

  (** Put differently, [{{l}}] is equivalent to [l]. *)
  Lemma undup_equivalent l : {{l}} ≈ l.
  Proof. intros x;apply In_undup. Qed.
  
  (** The [{{}}] operator always produces a duplication free list. *)
  Lemma NoDup_undup l : NoDup {{l}}.
  Proof.
    induction l;simpl;auto using NoDup_nil.
    case_in a {{l}};auto using NoDup_cons.
  Qed.

  (** The [{{}}] operator doesn't change duplication free lists. *)
  Lemma NoDup_undup_eq l : NoDup l -> l = {{l}}.
  Proof.
    induction l;simpl;auto.
    intro h;apply NoDup_cons_iff in h as (I&h).
    apply IHl in h as <-;case_in a l;tauto.
  Qed.

  (** A list is without duplication if and only if its mirror is duplication free. *)
  Lemma NoDup_rev {X:Set} (l : list X) : NoDup l <-> NoDup (rev l).
  Proof.
    induction l;simpl;firstorder.
    - apply NoDup_cons_iff in H1 as (I&h1).
      apply NoDup_app;firstorder;simpl.
      + simpl_In in *;intros [->|?];tauto.
      + apply NoDup_cons;firstorder;apply NoDup_nil.
    - apply NoDup_remove in H1 as (h1&h2);rewrite app_nil_r in *;apply H0 in h1.
      simpl_In in *;apply NoDup_cons;auto.
  Qed.

  (** [{{}}] preserves both [⊆] and [≈]. *)
  Global Instance undup_incl_Proper : Proper (@incl A ==> @incl A) undup.
  Proof. intros l m I x;simpl_In;auto. Qed.
  Global Instance undup_equivalent_Proper : Proper (@equivalent A ==> @equivalent A) undup.
  Proof. intros l m I x;simpl_In;auto. Qed.

  (** If [l] is contained in [m] and doesn't contain duplicates, then it must be shorter than [m]. *)
  Lemma NoDup_length (l m : list A) :
    l ⊆ m -> NoDup l -> ⎢l⎥ <= ⎢m⎥ .
  Proof.
    revert m;induction l;rsimpl;intros m E ND.
    - lia.
    - cut (⎢l⎥ <= ⎢(fun x=> negb (x=?=a)) :> m⎥).
      + intro L;eapply Lt.lt_le_S,PeanoNat.Nat.le_lt_trans;[apply L|].
        assert (Ia : a ∈ m) by (apply E;now left);revert Ia;clear.
        induction m as [|b m];simpl;[tauto|].
        intros [->|Ia].
        * rewrite eqX_refl;rsimpl;auto.
          apply Lt.le_lt_n_Sm,filter_length.
        * apply IHm in Ia;destruct_eqX b a;rsimpl;lia.
      + apply NoDup_cons_iff in ND as (Ia&ND).
        apply IHl;auto.
        rewrite <- E;simpl;rewrite eqX_refl;simpl.
        intro x;simpl_In; rewrite negb_true_iff,eqX_false.
        intros I;split;auto.
        intros ->;tauto.
  Qed.

  (** [l] is a fixpoint of [map f] if and only if [{{l}}] is a fixpoint of the same list homomorphism [map f]. *)
  Lemma map_undup_id (l : list A) (f : A -> A) :
    map f l = l <-> map f {{l}} = {{l}}.
  Proof.
    repeat rewrite map_eq_id.
    setoid_rewrite In_undup;tauto.
  Qed.

  (** If [f] is injective, [map f] and [{{}}] commute. *)
  Lemma map_undup_inj (l : list A) (f : A -> A) :
    (forall x y, f x = f y -> x = y) -> map f {{l}} = {{map f l}}.
  Proof.
    intro hp;induction l;auto.
    simpl;case_in a {{l}};case_in (f a) {{map f l}};simpl;rewrite IHl;auto;exfalso.
    - apply I0,In_undup,in_map_iff;exists a;simpl_In in I;tauto.
    - apply I;simpl_In in *.
      apply in_map_iff in I0 as (y&Ey&Iy);apply hp in Ey as ->;auto.
  Qed.

  (** [NoDup] is a decidable property. *)
  Definition NoDupb l := l =?= {{l}}.
  
  Lemma NoDupb_NoDup l : NoDupb l = true <-> NoDup l.
  Proof.
    unfold NoDupb;rewrite eqX_correct;split.
    + intros ->;apply NoDup_undup.
    + apply NoDup_undup_eq.
  Qed.

  (** Remove an element from a list. *)
  Definition rm (a : A) l := (fun x => negb (a=?=x)) :> l.
  Notation " l ∖ a " := (rm a l) (at level 50).

  Lemma rm_In b a l : b ∈ l ∖ a <-> b ∈ l /\ a<>b.
  Proof. unfold rm;rewrite filter_In,negb_true_iff,eqX_false;tauto. Qed.

  Lemma rm_equiv a l : a ∈ l -> l ≈ a::(l ∖ a).
  Proof. intros I x;simpl;rewrite rm_In;destruct_eqX a x;tauto. Qed.

  Global Instance rm_equivalent_Proper a : Proper ((@equivalent A)==> (@equivalent A)) (rm a).
  Proof. apply filter_equivalent_Proper. Qed.
  
  Global Instance rm_incl_Proper a : Proper ((@incl A)==> (@incl A)) (rm a).
  Proof. apply filter_incl_Proper. Qed.

  Lemma rm_notin a l : ~ a ∈ l -> l ∖ a = l.
  Proof.
    unfold rm;intro I.
    erewrite filter_ext_In;[apply filter_true|].
    intros b Ib.
    apply eq_true_iff_eq;split;[tauto|].
    intros _;apply negb_true_iff,eqX_false.
    intros ->;tauto.
  Qed.

  (** Remove the first occurrence of an element from a list. *)

  Fixpoint rmfst (a : A) l :=
  match l with
  | [] => []
  | b::l => if a=?=b then l else b::(rmfst a l)
  end.
  Notation " l ⊖ a " := (rmfst a l) (at level 50).

  Lemma rmfst_notin a l : ~ a ∈ l -> l ⊖ a = l.
  Proof.
    induction l;simpl;auto.
    intros N;simpl.
    destruct_eqX a a0.
    - exfalso;apply N;tauto.
    - f_equal;apply IHl;intro;tauto.
  Qed.

  Lemma rmfst_in a l1 l2 : ~ a ∈ l1 -> (l1 ++ a :: l2) ⊖ a = l1++l2.
  Proof.
    induction l1;simpl;auto.
    - rewrite eqX_refl;auto.
    - intros N;destruct_eqX a a0.
      + exfalso;apply N;tauto.
      + f_equal;apply IHl1;tauto.
  Qed.

  (** [l ⊖ a] is contained in the list [l]. *)
  Lemma rmfst_decr a l : l ⊖ a ⊆ l.
  Proof.
    case_in a l.
    - apply decomposition in I as (?&?&->&I).
      rewrite rmfst_in;auto;intro;simpl_In;simpl;tauto.
    - rewrite rmfst_notin;auto;reflexivity.
  Qed.

  (** The operation [rmfst] commutes with itself. *)
  Lemma rmfst_comm (l : list A) a b : (l ⊖ a) ⊖ b = (l ⊖ b) ⊖ a.
  Proof.
    induction l as [|c l];simpl;auto.
    destruct_eqX a c;subst.
    - destruct_eqX b c;auto.
      simpl;rewrite eqX_refl;reflexivity.
    - simpl;destruct_eqX b c;auto.
      simpl;apply eqX_false in N as ->.
      rewrite IHl;reflexivity.
  Qed.

  (** If we try to remove [a] from [l++m], one of three things may happen:
      - [a] appears in [l], so we obtain [(l⊖ a)++m];
      - [a] appears in [m] but not in [l], so we obtain [l++(m⊖ a)];
      - [a] does not appear in [l] or [m], so we obtain [l++m].
   *)
  Lemma rmfst_app_dec (l m:list A) a :
    (exists l1 l2, l = l1++a::l2 /\ ~ a ∈ l1 /\ (l++m) ⊖ a = l1++l2++m)
    \/ (exists m1 m2, m = m1++a::m2 /\ ~ a ∈ (l++m1) /\ (l++m) ⊖ a = l++m1++m2)
    \/ (~ a ∈ (l++m) /\ (l++m) ⊖ a = l++m).
  Proof.
    case_in a l.
    - left;apply decomposition in I as (l1&l2&->&I).
      exists l1,l2;repeat split;auto.
      rewrite app_ass;apply rmfst_in;auto.
    - case_in a m.
      + right;left;apply decomposition in I0 as (m1&m2&->&I0).
        exists m1,m2;simpl_In;repeat split;try tauto.
        repeat rewrite <-app_ass;apply rmfst_in;simpl_In;tauto.
      + right;right;rewrite rmfst_notin;simpl_In;tauto.
  Qed.

  (** This lemma highlights the existence of a list [l1-l2]: the list [m] shown to exist here is such that it contains no elements from [l1], but concatenating [l1] and [m] yields a list equivalent to [l1++l2]. Furthermore, we produce [m] without inserting any duplicates. *)
  Lemma split_app_unambiguous (l1 l2 : list A) :
    exists m, l1++l2 ≈ l1++m /\ NoDup m /\ (forall a, a ∈ m -> ~ a ∈ l1).
  Proof.
    induction l2 as [|b l];simpl.
    - exists [];repeat split;try tauto.
      apply NoDup_nil.
    - destruct IHl as (m&Em&nd&F).
      case_in b (l1++m).
      + exists m;split;[|split];try assumption.
        rewrite <- Em;clear F nd.
        intro;simpl_In in *;firstorder subst.
        * tauto.
        * cut (x∈(l1++l));[simpl_In;tauto|].
          rewrite Em;simpl_In;tauto.
      + exists (b::m);split;[|split].
        * transitivity (b::l1++l);[intro;repeat (simpl;simpl_In);tauto|].
          transitivity (b::l1++m);[|intro;repeat (simpl;simpl_In);tauto].
          rewrite Em;reflexivity.
        * apply NoDup_cons;[|assumption].
          intro I';apply I;simpl_In;tauto.
        * intros a [<-|Ia].
          -- intro Ib;apply I;simpl_In;tauto.
          -- apply F,Ia.
  Qed.

  (** Sometimes we will need to count the number of occurrences of a particular element in a given list. *)
  Notation nb a l := ⎢eqX a :> l⎥.

  (** An equivalent (but slightly less convenient) function was defined in the standard library. *)
  Lemma nb_count_occ (a : A) l : nb a l = count_occ X_dec l a.
  Proof.
    induction l;simpl;auto.
    destruct_eqX a0 a;rsimpl;auto.
    destruct_eqX a a0;subst;rsimpl;tauto.
  Qed.

  (** For convenience, we translate all the lemmas regarding [count_occ] in terms of [nb]. *)
  Lemma nb_nil (x : A) : nb x [] = 0.
  Proof. rewrite nb_count_occ;apply count_occ_nil. Qed.

  Lemma nb_In l (x : A) : x ∈ l <-> nb x l > 0.
  Proof. rewrite nb_count_occ;apply count_occ_In. Qed.
  
  Lemma nb_not_In (l : list A) (x : A): ~ x ∈ l <-> nb x l = 0.
  Proof. rewrite nb_count_occ;apply count_occ_not_In. Qed.
  
  Lemma NoDup_nb (l : list A) : NoDup l <-> (forall x : A, nb x l <= 1).
  Proof. setoid_rewrite nb_count_occ;apply NoDup_count_occ. Qed.

  Lemma nb_inv_nil (l : list A) : (forall x : A, nb x l = 0) <-> l = [].
  Proof. setoid_rewrite nb_count_occ;apply count_occ_inv_nil. Qed.

  Lemma nb_cons_neq (l : list A) (x y : A) : x <> y -> nb y (x :: l) = nb y l.
  Proof. repeat rewrite nb_count_occ;apply count_occ_cons_neq. Qed.

  Lemma nb_cons_eq (l : list A) (x y : A) : x = y -> nb y (x :: l) = S (nb y l).
  Proof. repeat rewrite nb_count_occ;apply count_occ_cons_eq. Qed.

  Lemma NoDup_nb' (l : list A) : NoDup l <-> (forall x : A, x ∈ l -> nb x l = 1).
  Proof. setoid_rewrite nb_count_occ;apply NoDup_count_occ'. Qed.


  (** If [l] is contained in [m] and if [m] has no duplicates, then the length of [l] can be obtained by summing over [m] the function that maps [a] to the number of occurrences of [a] in [l]. *)
  Lemma length_sum_filter l m:
    l ⊆ m -> NoDup m -> ⎢l⎥ = sum (fun a => nb a l) m.
  Proof.
    induction l.
    - simpl;intros.
      induction m;simpl;auto.
      apply IHm.
      + intro;simpl;tauto.
      + apply NoDup_cons_iff in H0;tauto.
    - intros I N.
      assert (IH : l ⊆ m) by (intros x h;apply I;now right).
      apply IHl in IH;auto;clear IHl.
      replace ⎢a::l⎥ with (S ⎢l⎥) by reflexivity.
      rewrite IH;clear IH.
      assert (Ia : a ∈ m) by (apply I;now left).
      apply in_split in Ia as (m1&m2&->).
      repeat rewrite sum_app.
      rsimpl;rewrite (@sum_ext_In _ _ (fun b =>  nb b (a::l))),
             (@sum_ext_In _ _ (fun b => nb b (a::l)) m2).
      + simpl;rewrite eqX_refl;rsimpl;lia.
      + intros;rsimpl.
        destruct_eqX x a;subst;auto.
        exfalso;apply NoDup_remove_2 in N.
        apply N,in_app_iff;tauto.
      + intros;simpl.
        destruct_eqX x a;subst;auto.
        exfalso;apply NoDup_remove_2 in N.
        apply N,in_app_iff;tauto.
  Qed.    

  Lemma sum_incr_0_left f (l m : list A) :
    (forall x, ~ x ∈ l -> f x = 0) -> sum f {{l}} = sum f {{m++l}}.
  Proof.
    intros;induction m;simpl.
    - reflexivity.
    - case_in a {{m++l}}.
      + assumption.
      + rewrite IHm.
        simpl;rewrite H;[lia|].
        intro I';apply I;simpl_In;tauto.
  Qed.

  Lemma sum_incr_0_right f (l m : list A) :
    (forall x, ~ x ∈ l -> f x = 0) -> sum f {{l}} = sum f {{l++m}}.
  Proof.
    intros h;rewrite (sum_incr_0_left m h).
    apply sum_eq_ND.
    - rewrite app_comm;reflexivity.
    - apply NoDup_undup.
    - apply NoDup_undup.
  Qed.

    (** A list [m] appears in [shuffles l] exactly when for every [a:A] there are as may occurrences of [a] in [l] as in [m]. *)
  Lemma shuffles_spec (m l : list A) : m ∈ shuffles l <-> forall a, nb a l = nb a m.
  Proof.
    revert m;induction l as [|b l];intros m;simpl.
    - split.
      + intros [<-|F];[|tauto].
        intro a;reflexivity.
      + destruct m as [|c m];[tauto|].
        intros h;simpl.
        pose proof (h c) as e;revert e.
        simpl;simpl_beq;simpl.
        discriminate.
    - rewrite in_flat_map;setoid_rewrite IHl;setoid_rewrite insert_spec;split.
      + intros (l'&h&l1&l2&->&->) a.
        pose proof (h a) as e.
        rewrite filter_app in *;rsimpl in *.
        clear IHl h;destruct_eqX a b;rsimpl;lia.
      + intros h.
        exists (m ⊖ b);case_in b m.
        * apply decomposition in I as (l1&l2&->&I).
          rewrite rmfst_in;auto;split.
          -- intros a;pose proof (h a) as e;revert e;clear.
             destruct_eqX a b;simpl.
             ++ repeat rewrite filter_app.
                repeat rewrite app_length in *;simpl.
                simpl_beq;rsimpl.
                lia.
             ++ repeat rewrite filter_app.
                repeat rewrite app_length in *;simpl.
                simpl_beq;simpl.
                lia.
          -- eauto.
        * pose proof (h b) as e;revert e.
          simpl_beq;simpl.
          apply nb_not_In in I as ->.
          rewrite <- SizeLength;simpl;discriminate.
  Qed.

  (** Intersection of finite sets *)
  Definition intersect u v := (fun a => inb a v) :> u.
  Infix " ∩ " := intersect (at level 50).

  Lemma intersect_spec u v a : a ∈ u ∩ v <-> a ∈ u /\ a ∈ v.
  Proof. unfold intersect;simpl;simpl_In;rewrite inb_spec;tauto. Qed.

  Global Instance intersect_proper_incl :
    Proper (@incl _ ==> @incl _ ==> @incl _) intersect.
  Proof.
    intros l1 l2 el m1 m2 em a.
    repeat rewrite intersect_spec.
    intros;split;[apply el|apply em];tauto.
  Qed.

  Global Instance intersect_proper :
    Proper (@equivalent _ ==> @equivalent _ ==> @equivalent _) intersect.
  Proof.
    intros l1 l2 el m1 m2 em a.
    repeat rewrite intersect_spec.
    rewrite el,em;tauto.
  Qed.

  Lemma interect_nil u : u ∩ [] = [].
  Proof. apply incl_l_nil;intro;rewrite intersect_spec;simpl;tauto. Qed.

  Lemma intersect_app_l u v w : (u++v) ∩ w = (u∩w)++(v∩w).
  Proof. induction u;simpl;[|rewrite IHu;case_in a w];reflexivity. Qed.

  Lemma intersect_app_r u v w : u∩(v++w) ≈ (u∩v)++(u∩w).
  Proof. intro;repeat simpl_In||rewrite intersect_spec;tauto. Qed.

  Lemma intersect_ass u v w : u ∩ (v ∩ w) = (u ∩ v) ∩ w.
  Proof.
    induction u;simpl;[reflexivity|rewrite IHu].
    case_in a v;simpl.
    + case_in a w;case_in a (v∩w);simpl.
      * reflexivity.
      * exfalso;apply I1,intersect_spec;tauto.
      * exfalso;apply intersect_spec in I1;tauto.
      * reflexivity.
    + case_in a (v∩w);simpl.
      * exfalso;apply intersect_spec in I0;tauto.
      * reflexivity.
  Qed.
  Lemma intersect_comm u v : u ∩ v ≈ v ∩ u.
  Proof. intro a;repeat rewrite intersect_spec; tauto. Qed.

  Lemma intersect_meet_l u v : u ⊆ v -> u ∩ v = u.
  Proof.
    induction u as [|a u];intros huv;[reflexivity|].
    simpl;case_in a v.
    - rewrite IHu;[reflexivity|].
      intros b hb;apply huv;now right.
    - exfalso;apply I,huv;now left.
  Qed.

  Lemma intersect_incl u v : u ∩ v ⊆ u.
  Proof. intro a;rewrite intersect_spec;tauto. Qed.
    
  (** Difference of finite sets *)
  Definition difference u v := (fun a => negb (inb a v)) :> u.
  Infix " − " := difference (at level 50).

  Lemma difference_spec u v a : a ∈ u − v <-> a ∈ u /\ ~ a ∈ v.
  Proof.
    unfold difference;simpl;simpl_In.
    rewrite negb_true_iff,<-not_true_iff_false,inb_spec;tauto.
  Qed.

  Global Instance difference_proper :
    Proper (@equivalent _ ==> @equivalent _ ==> @equivalent _) difference.
  Proof.
    intros l1 l2 el m1 m2 em a.
    repeat rewrite difference_spec.
    rewrite el,em;reflexivity.
  Qed.
  
  Global Instance difference_proper_inf :
    Proper (@incl _ ==> Basics.flip (@incl _) ==> @incl _) difference.
  Proof.
    intros l1 l2 el m1 m2 em a.
    repeat rewrite difference_spec.
    rewrite el,em;tauto.
  Qed.

  Remark difference_right_subs u v w : u ≈ v -> w − u = w − v.
  Proof.
    intros e;induction w as [|a w];[reflexivity|].
    simpl;case_in a u;case_in a v;simpl;
      rewrite (e a) in *;rewrite IHw;reflexivity||tauto.
  Qed.
    
  Lemma difference_app_l u v w : (u++v)−w = (u−w)++(v−w).
  Proof.
    now induction u as [|a u];[|simpl;case_in a w;simpl;rewrite IHu].
  Qed.
  Lemma difference_app_r u v w : u−(v++w) ≈ (u−v)∩(u−w).
  Proof.
    intro a;repeat rewrite difference_spec
            ||rewrite intersect_spec||simpl_In.
    tauto.
  Qed.
  Lemma difference_inter_r u v w : u−(v∩w) ≈ (u−v)++(u−w).
  Proof.
    intro a;repeat rewrite difference_spec
            ||rewrite intersect_spec||simpl_In.
    case_in a v;tauto.
  Qed.
  Lemma difference_inter_l u v w : (u∩v)−w ≈ (u−w)∩(v−w).
  Proof.
    intro a;repeat rewrite difference_spec
            ||rewrite intersect_spec||simpl_In;tauto.
  Qed.
  Lemma difference_nil u : u − [] = u.
  Proof. now induction u as [|a u];simpl;[|rewrite IHu]. Qed.

  Lemma difference_incl u v : u − v ⊆ u.
  Proof. intro a;rewrite difference_spec;tauto. Qed.

  Lemma difference_intersect u v : v ∩ (u − v) = [].
  Proof.
    apply incl_l_nil;intro;rewrite intersect_spec,difference_spec.
    simpl;tauto.
  Qed.

End dec_list.
Notation " l ∖ a " := (rm a l) (at level 50).
Notation " l ⊖ a " := (rmfst a l) (at level 50).
Notation nb a l := ⎢eqX a :> l⎥.
Notation " {{ l }} " := (undup l) (at level 0).
Infix " ∩ " := intersect (at level 50).
  Infix " − " := difference (at level 50).

(* begin hide *)
Ltac case_in a l :=
  let I := fresh "I" in
  let E := fresh "E" in
  destruct (inb_dec a l) as [(E&I)|(E&I)];
  try rewrite E in *;clear E.
Lemma in_cons_iff {A} (l : list A) a b :
  a ∈ (b::l) <-> b = a \/ a ∈ l.
Proof. simpl;tauto. Qed.
Ltac simpl_In :=
  repeat rewrite in_app_iff
  || rewrite in_cons_iff
  || rewrite <- In_rev
  || rewrite In_undup
  || rewrite filter_In.
Tactic Notation "simpl_In" "in" hyp(h) :=
  repeat (rewrite in_app_iff in h)
  || (rewrite in_cons_iff in h)
  || (rewrite <- In_rev in h)
  || (rewrite In_undup in h)
  || (rewrite filter_In in h).
Tactic Notation "simpl_In" "in" "*" :=
  repeat (rewrite in_app_iff in * )
  || (rewrite in_cons_iff in * )
  || (rewrite <- In_rev in * )
  || (rewrite In_undup in * )
  || (rewrite filter_In in * ).
(* end hide *)

Lemma nb_map {A B :Set} `{decidable_set A,decidable_set B} (f : A -> B) :
  (forall x1 x2 : A, f x1 = f x2 -> x1 = x2) ->
  forall (x : A) (l : list A), nb x l = nb (f x) (map f l).
Proof. setoid_rewrite nb_count_occ;apply count_occ_map. Qed.

Lemma rmfst_flip {A B : Set} `{decidable_set A,decidable_set B} (s : list (A*B)) a b :
  s` ⊖ (a,b) = (s ⊖ (b,a))`.
Proof.
  case_in (b,a) s.
  - rewrite decomposition in I;destruct I as (s1&s2&->&I).
    rewrite rmfst_in;auto.
    rewrite flip_app;simpl.
    rewrite rmfst_in,flip_app;auto.
    rewrite In_flip;apply I.
  - rewrite rmfst_notin,rmfst_notin;auto.
    rewrite In_flip;apply I.
Qed.

(** [insert] commutes with [map]. *)
Lemma insert_map {A B : Set} `{decidable_set A,decidable_set B} :
  forall (f : A -> B) l a, insert (f a) (map f l) = map (map f) (insert a l).
Proof.
  intro f;induction l as [|b l];intro a;simpl.
  - reflexivity.
  - rewrite IHl,map_map,map_map.
    f_equal.
Qed.

(** [shuffles] commutes with [map]. *)
Lemma shuffles_map {A B : Set} `{decidable_set A,decidable_set B} :
  forall (f : A -> B) l, shuffles (map f l) = map (map f) (shuffles l).
Proof.
  intro f;induction l as [|a l];simpl.
  - reflexivity.
  - rewrite IHl,flat_map_concat_map,flat_map_concat_map.
    rewrite map_map,concat_map,map_map.
    f_equal;apply map_ext.
    intros;apply insert_map.
Qed.

Global Instance DecidableProp_In (A : Set) (x : A) l :
  decidable_set A -> DecidableProp (x ∈ l).
Proof. intro;case_in x l;[left|right];assumption. Qed.
Global Instance DecidableProp_Incl (A : Set) (l m : list A) :
  decidable_set A -> DecidableProp (l ⊆ m).
Proof.
  intro;case_eq (inclb l m);intro h;[left|right];
    revert h;[|rewrite <- not_true_iff_false];rewrite inclb_correct;tauto.
Qed.
Global Instance DecidableProp_Equiv (A : Set) (l m : list A) :
  decidable_set A -> DecidableProp (l ≈ m).
Proof.
  intro;case_eq (equivalentb l m);intro h;[left|right];
    revert h;[|rewrite <- not_true_iff_false];rewrite equivalentb_spec;tauto.
Qed.
