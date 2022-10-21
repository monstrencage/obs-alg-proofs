Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Import sem_obs fan.

Section s.
  Context {G : Graph}
          {decG : DecidableGraph G}
          {fanG : FanGraph G}.
    
  Definition impl_lst u v := flat_map an u ++ v.
  Lemma impl_lst_spec a u v :
    a ∈ impl_lst u v <-> (exists b, b ∈ u /\ a ⌣ b) \/ a ∈ v.
  Proof.
    unfold impl_lst;rewrite in_app_iff,in_flat_map.
    setoid_rewrite an_spec;reflexivity.
  Qed.

  Fixpoint support s :=
    match s with
    | ⊥o | ⊤o => []
    | ⦑a⦒ => [a]
    | s ⟇ t | s ⟑ t => support s ++ support t
    | s → t => impl_lst (support s) (support t)
    end.
  Notation " ⎣ s ⎦ " := (support s).
  
  Lemma support_dominates_sem s x :
    x ⊨ s <-> ! (⎣ s ⎦ @@ x) ⊨ s.
  Proof.
    revert x;induction s;intro x;simpl;rsimpl.
    - tauto.
    - tauto.
    - etransitivity;[|symmetry;apply fc_to_clique_spec].
      rewrite project_spec;simpl;tauto.
    - rewrite (IHs1 (! _)),(IHs2 (! _)).
      pose proof (@project_project _ _ ⎣s1⎦ (⎣s1⎦++⎣s2⎦) x) as e.
      apply fc_to_clique_proper_eq in e as ->.
      pose proof (@project_project _ _ ⎣s2⎦ (⎣s1⎦++⎣s2⎦) x) as e.
      apply fc_to_clique_proper_eq in e as ->.
      rewrite intersect_meet_l by (apply incl_appl;reflexivity).
      rewrite intersect_meet_l by (apply incl_appr;reflexivity).
      rewrite IHs1,IHs2;reflexivity.
    - rewrite (IHs1 (! _)),(IHs2 (! _)).
      pose proof (@project_project _ _ ⎣s1⎦ (⎣s1⎦++⎣s2⎦) x) as e.
      apply fc_to_clique_proper_eq in e as ->.
      pose proof (@project_project _ _ ⎣s2⎦ (⎣s1⎦++⎣s2⎦) x) as e.
      apply fc_to_clique_proper_eq in e as ->.
      rewrite intersect_meet_l by (apply incl_appl;reflexivity).
      rewrite intersect_meet_l by (apply incl_appr;reflexivity).
      rewrite IHs1,IHs2;reflexivity.
    - unfold ssmaller. 
      setoid_rewrite fc_to_clique_spec.
      setoid_rewrite project_spec.
      setoid_rewrite impl_lst_spec.
      split.
      + intros h1 y hy1 h2.
        cut (exists z : clique, x ≲ z
                           /\ ⎣s2⎦@@y ⊃f (⎣s2⎦@@z)
                           /\ ⎣s1⎦@@z ⊃f (⎣s1⎦@@y)).
        * intros (z&hz1&hz2&hz3);apply IHs2.
          apply fc_to_clique_iff in hz2.
          rewrite <- hz2,<-IHs2.
          apply h1,hz1. 
          apply IHs1.
          apply fc_to_clique_iff in hz3.
          rewrite <- hz3,<-IHs1.
          apply hy1.             
        * clear h1 hy1 IHs1 IHs2.
          destruct (decidable_incompatible_with_fcliques x (⎣s1⎦@@y))
            as [i|i].
          -- destruct i as (a&b&ha&hb&hab).
             rewrite fc_to_clique_spec, project_spec in hb.
             exfalso.
             apply hab,(members_are_coh y);[|tauto].
             apply h2;split;[|left;exists b];tauto.
          -- apply not_incompatible_is_joins in i as (z&hz).
             pose proof hz as e.
             apply joins_is_meet in e as (e1&e2&e3).
             exists z;split;[|split].
             ++ apply e1.
             ++ intros a;unfold satisfies;repeat rewrite project_spec.
                intros (ha1&ha2);split;[|assumption].
                apply hz in ha1 as [ha1|ha1].
                ** apply h2; tauto.
                ** apply fc_to_clique_spec,project_spec in ha1;tauto.
             ++ transitivity ($ (⎣s1⎦ @@ !(⎣s1⎦@@ y))).
                ** rewrite project_project,intersect_meet_l;reflexivity.
                ** apply project_proper_inf,e2;reflexivity.
      + intros h y h1 h2;apply h;[assumption|].
        intros;apply h2;tauto.
  Qed.

  Instance finSat : Satisfaction fcliques observation :=
    fix fsatisfies (x : fcliques) (o : observation) :=
      match o with
      | ⊤o  => True
      | ⊥o => False
      | ⦑u⦒ => u ∈ $ x
      | o1 ⟇ o2 => fsatisfies x o1 \/ fsatisfies x o2
      | o1 ⟑ o2 => fsatisfies x o1 /\ fsatisfies x o2
      | o1 → o2 =>
          forall y, fsatisfies y o1 ->
               x ↯↯ y \/ exists z, fjoins x y z /\ fsatisfies z o2
      end.

  Remark fsat_top x : x ⊨ ⊤o <-> True.
  Proof. reflexivity. Qed.
  Remark fsat_bot x : x ⊨ ⊥o <-> False.
  Proof. reflexivity. Qed.
  Remark fsat_at x u : x ⊨ ⦑u⦒ <-> u ⊨ x.
  Proof. reflexivity. Qed.
  Remark fsat_disj x o1 o2 : x ⊨ (o1 ⟇ o2) <-> x ⊨ o1 \/ x ⊨ o2.
  Proof. reflexivity. Qed.
  Remark fsat_conj x o1 o2 : x ⊨ (o1 ⟑ o2) <-> x ⊨ o1 /\ x ⊨ o2.
  Proof. reflexivity. Qed.
  Remark fsat_impl x o1 o2 :
    x ⊨ (o1 → o2) <->
      (forall y, y ⊨ o1 -> x ↯↯ y \/ exists z, fjoins x y z /\ z ⊨ o2).
  Proof. reflexivity. Qed.
  
  Proposition fcliques_sat_iff_fsat s (α : fcliques) :
    ! α ⊨ s <-> α ⊨ s.
  Proof.
    revert α;induction s; simpl;auto;try tauto.
    - intro;apply fc_to_clique_spec.
    - intro a;rsimpl.
      rewrite IHs1,IHs2;reflexivity.
    - intro a;rsimpl;rewrite IHs1,IHs2;reflexivity.
    - intro α;rsimpl;rewrite fsat_impl;split.
      + intros h y hy.
        destruct (incompatible_or_joins_f α y) as [h'|(j&hj)];[tauto|].
        right;exists j;split;[assumption|].
        apply IHs2.
        pose proof hj as hh;apply joins_is_meet_f in hh as (hzx&hzy&hm).
        apply h.
        * apply fc_to_clique_iff in hzy.
          rewrite <-hzy;apply IHs1;assumption.
        * apply fc_to_clique_iff,hzx.
      + intros h y hys hya.
        apply support_dominates_sem in hys.
        apply IHs1 in hys.
        apply h in hys as [hys|(z&hz&hys)].
        * destruct hys as (a&b&ha&hb&i).
          apply fc_to_clique_spec,hya in ha.
          apply project_spec in hb as (hb1&hb2).
          exfalso;apply i,(members_are_coh y a b);assumption.
        * pose proof hz as hz'.
          apply joins_is_meet_f in hz' as (h1&h2&h3).
          apply IHs2 in hys.
          cut (!z ≲ y);[intros <-;assumption|].
          intros a ha.
          apply fc_to_clique_spec,hz,in_app_iff in ha as [ha|ha].
          -- apply hya,fc_to_clique_spec,ha.
          -- apply project_spec in ha; tauto.
  Qed.

  Corollary clique_sat_iff_fsat_proj s (α : clique) :
    α ⊨ s <-> (⎣s⎦ @@ α) ⊨ s.
  Proof.
    rewrite support_dominates_sem,fcliques_sat_iff_fsat.
    reflexivity.
  Qed.

  Corollary incl_sem_iff_incl_fin_sem s t :
    @ssmaller _ clique _ s t <-> @ssmaller _ fcliques _ s t.
  Proof.
    split;intros h α hα.
    - apply fcliques_sat_iff_fsat,h,fcliques_sat_iff_fsat,hα.
    - rewrite <-project_larger.
      apply fcliques_sat_iff_fsat,h,clique_sat_iff_fsat_proj,hα.
  Qed.
  
End s.
