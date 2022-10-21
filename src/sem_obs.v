Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Export syntax_obs equiv_obs.

Section s.
  Context {G : Graph} {decG : DecidableGraph G}.
  (** * Semantics of observation terms *)

  (** The semantics is given by a satisfaction relation, specifying which cliques belong to the language of a term. *)
  Global Instance satObs : Satisfaction clique observation :=
    fix satObs (x : clique) (o : observation) :=
      match o with
      | ⊤o  => True
      | ⊥o => False
      | ⦑u⦒ => u ⊨ x
      | o1 ⟇ o2 => satObs x o1 \/ satObs x o2
      | o1 ⟑ o2 => satObs x o1 /\ satObs x o2
      | o1 → o2 =>
          forall y, satObs y o1 -> y ⊃ x -> satObs y o2
      end.

  Remark sat_top x : x ⊨ ⊤o <-> True.
  Proof. reflexivity. Qed.
  Remark sat_bot x : x ⊨ ⊥o <-> False.
  Proof. reflexivity. Qed.
  Remark sat_at x u : x ⊨ ⦑u⦒ <-> u ⊨ x.
  Proof. reflexivity. Qed.
  Remark sat_disj x o1 o2 : x ⊨ (o1 ⟇ o2) <-> x ⊨ o1 \/ x ⊨ o2.
  Proof. reflexivity. Qed.
  Remark sat_conj x o1 o2 : x ⊨ (o1 ⟑ o2) <-> x ⊨ o1 /\ x ⊨ o2.
  Proof. reflexivity. Qed.
  Remark sat_impl x o1 o2 :
    x ⊨ (o1 → o2) <-> forall y, y ⊨ o1 -> y ⊃ x -> y ⊨ o2.
  Proof. reflexivity. Qed.

  Hint Rewrite sat_top sat_bot sat_at sat_disj sat_conj sat_impl
    : simpl_typeclasses.

  Global Instance satObs_proper :
    Proper (sequiv ==> sequiv ==> iff) satisfies.
  Proof.
    intros α β e s t E;rewrite <- E;clear t E;revert α β e.
    (* induction s;intros;repeat sat_simpl; try reflexivity. *)
    induction s;intros;rsimpl in *; try reflexivity.
    - simpl;rewrite (e v);reflexivity.
    - rewrite IHs1,IHs2;reflexivity||assumption.
    - rewrite IHs1,IHs2;reflexivity||assumption.
    - setoid_rewrite e;reflexivity.
  Qed.

  Global Instance satisfies_inf :
    Proper (ssmaller ==> ssmaller ==> Basics.impl) satisfies.
  Proof.
    unfold Basics.impl.
    intros α β e s t E;rewrite <- E;clear t E;revert α β e.
    induction s;intros α β e;rsimpl;try tauto.
    - apply e.  
    - intros [h|h].
      + left;apply (IHs1 _ _ e h).
      + right;apply (IHs2 _ _ e h). 
    - intros (h1&h2);split.
      + apply (IHs1 _ _ e h1).
      + apply (IHs2 _ _ e h2).
    - intros h y h1 h2.
      apply h.
      + assumption.
      + transitivity β;assumption.
  Qed.

  (** [n]-ary meets and joins. *)
  Lemma satisfies_Join x A : x ⊨ (⋁ A) <-> exists a, a ∈ A /\ x ⊨ a.
  Proof.
    induction A;rsimpl.
    - split;[|intros (_&F&_)];tauto.
    - rewrite IHA.
      split.
      + intros [h|(b&hb&h)].
        * exists a;tauto.
        * exists b;tauto.
      + intros (b&[->|hb]&h);[|right;exists b];auto.
  Qed.
  
  Lemma satisfies_Meet x A : x ⊨ (⋀ A) <-> forall a, a ∈ A -> x ⊨ a.
  Proof.
    induction A;rsimpl. 
    - split;tauto.
    - rewrite IHA.
      split.
      + intros (h1&h2) b [<-|hb];auto.
      + intros h;split;[|intros b hb];apply h;auto.
  Qed.

  (** Finite cliques *)
  Remark π_spec x y : x ⊨ (π y) <-> x ⊃ ! y.
  Proof.
    unfold π;rewrite satisfies_Meet.
    setoid_rewrite in_map_iff.
    split.
    - intros h u hu.
      cut (x ⊨ ⦑u⦒);[simpl;tauto|].
      revert hu;simpl_fc;intro hu.
      apply h;exists u;split;[reflexivity|assumption].
    - intros h a (u&<-&hu).
      apply h;simpl_fc;assumption.
  Qed.

  (** The problems of 1) satifiability for finite cliques 2) semantic containment of a pair of terms 3) semantic equivalence of a pair of terms are all equi-decidable. *)
  Remark dec_fsat_impl_dec_ssmaller :
    (forall α s, DecidableProp (!α ⊨ s)) -> forall s t, DecidableProp ( s ≲ t ).
  Proof.
    intros hdec s t.
    assert (ic : test (is_coherent []) = true)
      by (now apply test_spec;intro;simpl).
    case_prop (! (exist _ [] ic) ⊨ (s→t));[left|right].
    - intros α hα.
      rsimpl in *.
      apply hyp;[assumption|].
      intro a;rewrite fc_to_clique_spec;simpl;tauto.
    - intros h;apply hyp;clear hyp.
      rsimpl;intros α hα _;apply h,hα.
  Qed.
  Remark dec_ssmaller_impl_dec_fsat :
    (forall s t, DecidableProp ( s ≲ t )) -> (forall α s, DecidableProp (!α ⊨ s)).
  Proof.
    intros hdec α s.
    case_prop (π α ≲ s);[left|right].
    - apply hyp,π_spec;reflexivity.
    - intros h;apply hyp;clear hyp.
      intros β hβ.
      apply π_spec in hβ as <-.
      assumption.
  Qed.
  Remark dec_sequiv_impl_dec_ssmaller :
    (forall s t, DecidableProp (s ≃ t)) -> forall s t, DecidableProp ( s ≲ t ).
  Proof.
    intros hdec s t ;case_prop (s ⟇ t ≃ t);[left|right].
    - rewrite <- hyp;intro α;rsimpl;tauto.
    - intros h;apply hyp;clear hyp.
      intros α;rsimpl;split;[intros [];[apply h|]|];tauto.
  Qed.  
  Remark dec_ssmaller_impl_dec_sequiv :
    (forall s t, DecidableProp (s ≲ t)) -> forall s t, DecidableProp ( s ≃ t ).
  Proof.
    intros hdec s t ;case_prop (s ≲ t /\ t ≲ s);[left|right].
    - intro α;split;apply hyp.
    - intros h;apply hyp;clear hyp.
      rewrite h;split;reflexivity.
  Qed.

  (** The following property will be useful to combine observation algebras. *)
  Definition choose_clique :=
    forall (α : clique) (s t : observation),
      {forall β, β ⊃ α -> β ⊨ s -> β ⊨ t} + {exists β, β ⊃ α /\ β ⊨ s /\ ~ β ⊨ t}.

  (** It implies the decidability of satisfiability. *)
  Lemma choose_clique_sat_dec :
    choose_clique -> forall α s, DecidableProp (α ⊨ s).
  Proof.
    intros hyp α s.
    destruct (hyp α ⊤o s) as [h|h].
    - left;apply h;[reflexivity|exact I].
    - right;intro f.
      destruct h as (β&h1&_&h2).
      rewrite h1 in f;tauto.
  Qed.

End s.

Infix " ⊨ " := satisfies (at level 10).
Arguments choose_clique : clear implicits.
Global Hint Rewrite @sat_top @sat_bot @sat_at @sat_disj @sat_conj
       @sat_impl
    : simpl_typeclasses.

Proposition eo_sound `{Graph} 𝖠 :
  (subrelation 𝖠 sequiv) -> forall a b, 𝖠 ⊢ a ≡ b -> a ≃ b.
Proof.
  unfold sequiv;intros h a b E;induction E;intro x;simpl;rsimpl;try tauto.
  - rewrite (IHE);reflexivity. 
  - rewrite (IHE1),(IHE2);reflexivity.
  - rewrite (IHE1),(IHE2);reflexivity.
  - rewrite (IHE1),(IHE2);reflexivity.
  - setoid_rewrite <- (IHE1).
    setoid_rewrite <- (IHE2).
    reflexivity.
  - apply h;assumption.
Qed.

Proposition ha_sound `{Graph} : subrelation ha_ax sequiv.
Proof.
  unfold sequiv;intros a b E;destruct E;intro x;rsimpl;try tauto.
  - split;intros (h1&h2);split;auto.
    + apply h2;[assumption|reflexivity].
    + intros y h3 <-;assumption.
  - split;[tauto|intro h;split;[assumption|]].
    intros y h1 <-;assumption.
  - split;[intros h;split|intros (h1&h2)];intros y hya hyx.
    + apply h;assumption.
    + apply h;assumption.
    + split;[apply h1|apply h2];assumption.
Qed.

Proposition Obs_sound `{DecidableGraph} :
  subrelation Obs sequiv.
Proof.
  intros _ _ [s t E|s t [a b h]].
  - apply ha_sound,E.
  - intros x; split;simpl;rsimpl;[|tauto].
    intros (h1&h2);apply h,(members_are_coh x a b);assumption.
Qed.

Proposition Obs'_sound {G : Graph} {decG : DecidableGraph G} :
  subrelation Obs' sequiv.
Proof.
  intros _ _ [s t E| _ _ [s t E|_ _ [α s t|α a haα]]].
  - apply ha_sound,E.
  - apply Obs_sound,jright,E.
  - intros x;simpl;split.
    + intros h1.
      destruct (decidable_incompatible_with_fcliques x α)
        as [(a&b&ha&hb&hab)|i].
      * left;intros y h2 h3.
        exfalso;apply hab.
        apply (members_are_coh y).
        -- apply h3,ha.
        -- apply π_spec in h2.
           apply h2,hb.
      * apply not_incompatible_is_joins in i as (z&hz).
        cut (z ⊨ (s ⟇ t)).
           ++ intros [h|h];[left|right];intros y hyα hyx;
                eapply (@satisfies_inf _ z);
                try apply h;try apply reflexivity;
                  intro a;simpl;rewrite (hz a);
                    intros [I|I];auto.
              ** apply π_spec in hyα.
                 apply hyα,I.
              ** apply π_spec in hyα.
                 apply hyα,I.
           ++ simpl;apply h1;[apply π_spec|];
                intro a;simpl;rewrite (hz a);tauto.
    + intros [h|h] y h1 h2;[left|right];apply h;auto.
  - intros x;simpl.
    destruct (decidable_incompatible_with_fcliques x α)
        as [(b&c&hb&hc&hbc)|i].
    + split;[intro h;left|intros _];intros y h1 h2;apply π_spec in h1;
        [|exfalso];
        (apply hbc,(members_are_coh y);[apply h2|apply h1]);auto.
    + split.
      * rsimpl;setoid_rewrite π_spec.
        intro h;right.
        apply not_incompatible_is_joins in i as (z&hz).
        assert (!α ≲ z /\ x ≲ z) as (h1&h2).
        ++ split;intro b;rewrite (hz b);simpl;auto.
        ++ pose proof (h z h1 h2) as hz'.
           apply hz in hz' as [hz'|hz'];auto.
           exfalso;apply haα,inb_spec,Is_true_iff_eq_true,hz'.
      * intros [h|h] y h1 h2.
        -- exfalso;apply (h y h1 h2).
        -- apply h2,h.
Qed.

