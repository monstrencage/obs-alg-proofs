Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations list_dec decidable_prop.
Require Import equiv_obs sem_obs laws.

(** * Graphs with finite anti-neighbourhoods. *)

(** We define fan graphs as having an antineighbourhood function, mapping each vertex [a] to a list containing exactly those vertices [b] such that [a] and [b] are not connected, i.e. [a⌢b]. *)
Class FanGraph (G : Graph) :=
  {
  an : vertex -> list vertex;
  an_spec : forall a b, a ∈ an b <-> a ⌣ b
  }.

Section s.
  Context {G : Graph}
          {decG : DecidableGraph G}
          {FanG : FanGraph G}.
  
  Reserved Notation " x =fan y " (at level 80).

  Inductive fan_ax : relation observation :=
  | fan_clique_neg α :
      (π α → ⊥o) =fan ⋁ (map (fun a => ⦑a⦒) (flat_map an $α))
  where " x =fan y " := (fan_ax x y).
  Notation FAN := (ha_ax (+) (obs'_ax (+) fan_ax)).
  Hint Constructors fan_ax : core.

  Remark eo_fan_clique_neg α : 
    FAN ⊢ (π α → ⊥o) ≡ ⋁ (map (fun a => ⦑a⦒) (flat_map an $α)).
  Proof. auto with equiv_obs. Qed.
  
  Global Instance FAN_Obs :
    subrelation (equiv_Obs Obs') (equiv_Obs FAN).
  Proof with (auto with equiv_obs).
    intros s t h;induction h;subst...
    - etransitivity;eauto.
    - destruct H as [s t h|_ _ [_ _ [a b h]|s t h]]...
      rewrite  <- (var_clique b).
      apply eo_eq_bot_iff_inf_bot,eo_heyting.
      cut (FAN ⊢ ⦑ a ⦒ ≦ (π (sgl__f b) → ⊥o))...
      rewrite eo_fan_clique_neg;simpl.
      rewrite app_nil_r.
      apply eo_inf_in_Join;simpl.
      apply in_map_iff.
      exists a;split;auto.
      apply an_spec,h.
  Qed.

  Proposition FAN_sound : subrelation FAN sequiv.
  Proof.
    intros _ _ [s t h|_ _ [s t h|_ _ [α]]].
    - apply ha_sound,h.
    - apply Obs'_sound,jright,jright,h.
    - intro x;rsimpl;split.
      + intros h;apply satisfies_Join.
        destruct (decidable_incompatible_with_fcliques x α) as [hj|hj].
        * destruct hj as (a&b&ha&hb&i).
          apply fc_to_clique_spec in hb.
          exists ⦑a⦒;split;[apply in_map_iff;exists a;split;
                       [|apply in_flat_map;exists b;rewrite an_spec]
                      |];tauto.
        * exfalso;apply not_incompatible_is_joins in hj as (Φ&hϕ).
          apply joins_is_meet in hϕ as (hx&hα&_).
          apply (h Φ);[rewrite <-hα;apply π_spec;reflexivity|assumption].
      + intro h;apply satisfies_Join in h as (o&ho&hx);rsimpl.
        apply in_map_iff in ho as (a&<-&ha).
        apply in_flat_map in ha as (b&hb&I);apply an_spec in I.
        intros y h1 h2.
        apply π_spec in h1.
        apply inb_spec,Is_true_iff_eq_true in hb.
        apply h1 in hb.
        simpl in hx;apply h2 in hx.
        apply I,(members_are_coh y a b);assumption.
  Qed. 

  
  Lemma impl_cliques x y :
    FAN ⊢ π x → π y ≡ (π x → ⊥o) ⟇ ⋀ (map o_obs ($y − $ x)).
  Proof.
    unfold π at 2;destruct y as [y hy];simpl.
    rewrite Meet_impl,or_Meet.
    rewrite map_map.
    transitivity (⋀ (map (fun a : vertex => π x → ⦑ a ⦒)
                         (y − $x ++ y ∩ $x)));
      [apply Meet_equiv,map_equivalent_Proper;
       intro a;rewrite in_app_iff,difference_spec,intersect_spec;
       case_in a ($x);tauto|].
    rewrite map_app,Meet_app.
    etransitivity;[etransitivity;[apply eo_and;[reflexivity|]
                                 |apply eo_and_top]|].
    - apply eo_eq_top_iff_top_inf;unfold__lat.
      apply eo_heyting;rewrite eo_and_comm,eo_and_top.
      rewrite <-var_clique.
      apply π_proper;intro;simpl.
      apply intersect_spec in ha;intros [<-|];tauto.
    - apply Meet_map_equiv_pointwise.
      intros a ha;apply difference_spec in ha as (ha1&ha2).
      apply eo_ax,jright,jleft,obs_clique_obs,ha2.
  Qed.

  Lemma impl_disj x l :
    FAN ⊢ π x → ⋁ l ≡ (π x → ⊥o) ⟇ ⋁ (map (o_impl (π x)) l).
  Proof.
    induction l;simpl.
    - symmetry;apply eo_or_bot.
    - etransitivity;[apply eo_ax,jright,jleft,obs_clique_impl|].
      rewrite IHl.
      repeat rewrite eo_or_ass.
      apply eo_or;[apply eo_or_comm|reflexivity].
  Qed.

  Lemma impl_disj_cliques x l :
    FAN ⊢ (π x → ⋁ (map π l))
        ≡ (π x → ⊥o) ⟇ ⋁ (map (fun y => ⋀ (map o_obs ($y − $ x))) l).
  Proof.
    rewrite impl_disj,map_map.
    etransitivity;[apply eo_or;[reflexivity
                               |apply Join_map_equiv_pointwise;
                                intros y hy;apply impl_cliques]|].
    split_order;unfold__lat;try (apply eo_inf_or_left;reflexivity).
    - apply eo_inf_or_right,eo_inf_in_Join,in_map_iff.
      eexists;eauto.
    - apply eo_inf_or_right.
      etransitivity;[apply eo_inf_or_right;reflexivity
                    |apply eo_inf_in_Join,in_map_iff;exists a;tauto].
  Qed.

  Definition join__f (p : fcliques*fcliques) :
    { l : list fcliques |  FAN ⊢ ⋁ (map π l) ≡ π (fst p) ⟑ π(snd p) }.
    case_eq (test(is_coherent ($(fst p)++$(snd p))/\($(fst p)++$(snd p)<>[]))).
    - intros ic;exists [exist _ _ ic : fcliques].
      simpl;rewrite eo_or_bot.
      unfold π;simpl.
      rewrite map_app,Meet_app;reflexivity.
    - intros ic;exists [].
      simpl;symmetry;apply eo_eq_bot_iff_inf_bot.
      apply not_true_iff_false in ic.
      rewrite test_spec in ic.
      destruct p as [x y];simpl in *.
      case_prop (exists a b, a ∈ $x /\ b ∈ $ y /\ a ⌣ b).
      + destruct hyp as (a&b&h1&h2&h3).
        transitivity (⦑a⦒⟑⦑b⦒).
        * apply o_and_inf;apply eo_inf_in_Meet,in_map_iff;eexists;eauto.
        * rewrite <- eo_eq_bot_iff_inf_bot.
          apply FAN_Obs,eo_ax,jright,jleft,obs_incoh,h3.
      + exfalso;apply ic;split.
        * intros a b h1 h2.
          apply in_app_iff in h1,h2.
          destruct h1 as [h1|h1], h2 as [h2|h2];
            (eapply fcliques_coherent;eassumption)
            ||(case_prop (a ⁐ b);
              [assumption
              |exfalso;apply hyp;eexists;eexists;repeat split;eauto]).
          symmetry;apply hyp0.
        * case_eq ($x);[|simpl;discriminate].
          intros h _;revert h;apply fcliques_non_empty.
  Defined.
  
  Definition R := option (list fcliques).
  
  Definition τ (l : R) : observation :=
    match l with
    | None => ⊤o
    | Some l => ⋁ (map π l)
    end.
  
  Fixpoint Conj (L : list (list fcliques)) : R :=
    match L with
    | [] => None
    | l::L =>
        match Conj L with
        | None => Some l
        | Some r => Some (flat_map (fun p => $ (join__f p)) (pairs l r))
        end
    end.

  Lemma Conj_spec L :
    FAN ⊢ ⋀ (map (fun l => ⋁ (map π l)) L) ≡ τ (Conj L).
  Proof.
    induction L as [|l L];simpl;[reflexivity|].
    rewrite IHL;clear IHL.
    destruct (Conj L) as [C|];clear L;simpl.
    - rewrite Join_and_Join.
      rewrite flat_map_concat_map.
      rewrite concat_map,map_map.
      rewrite <-flat_map_concat_map.
      rewrite flat_map_Join,map_map.
      split_order.
      + unfold__lat;destruct a as (a1&a2);apply pairs_spec in ha
            as (ha1&ha2).
        apply in_map_iff in ha1 as (s&<-&hs).
        apply in_map_iff in ha2 as (t&<-&ht);simpl.
        transitivity (⋁ (map π ($ (join__f (s,t))))).
        * destruct (join__f (s,t)) as (x&hx);simpl.
          apply eq_obs_inf_obs;symmetry;apply hx.
        * apply eo_inf_in_Join,in_map_iff;exists (s,t);split;[reflexivity|].
          apply pairs_spec;tauto.
      + unfold_join.
        destruct a as (s&t);apply pairs_spec in ha as (hs&ht).
        destruct (join__f (s,t)) as (x&hx);simpl;rewrite hx;simpl.
        apply eo_inf_in_Join,in_map_iff;exists (π s,π t);split;[reflexivity|].
        apply pairs_spec;split;apply in_map_iff;eexists;eauto.
    - auto with equiv_obs.
  Qed.

  Definition orR : R -> R -> R :=
    fun r1 r2 =>
      match r1,r2 with
      | None,None
      | Some _,None
      | None, Some _=> None
      | Some l,Some m => Some (l++m)
      end.

  Lemma orR_spec r1 r2 : FAN ⊢ τ(orR r1 r2) ≡ τ r1 ⟇ τ r2. 
  Proof.
    destruct r1 as [l1|],r2 as [l2|];simpl.
    - rewrite map_app,Join_app;auto with equiv_obs.
    - auto with equiv_obs.
    - transitivity (⋁ (map π l2)⟇⊤o);auto with equiv_obs.
    - auto with equiv_obs.
  Qed.

  Definition andR : R -> R -> R :=
    fun r1 r2 =>
      match r1,r2 with
      | None,None=> None
      | Some l,None
      | None, Some l=> Some l
      | Some l,Some m => Conj [l;m]
      end.

  Lemma andR_spec r1 r2 : FAN ⊢ τ(andR r1 r2) ≡ τ r1 ⟑ τ r2. 
  Proof.
    destruct r1 as [l1|],r2 as [l2|].
    - unfold andR;rewrite <-Conj_spec;simpl.
      auto with equiv_obs.
    - simpl;auto with equiv_obs.
    - simpl;transitivity (⋁ (map π l2)⟑⊤o);auto with equiv_obs.
    - auto with equiv_obs.
  Qed.

  Definition atR a : R := Some [sgl__f a].
  Lemma atR_spec a : FAN ⊢ τ (atR a) ≡ ⦑a⦒.
  Proof. simpl;rewrite var_clique;auto with equiv_obs. Qed.

  Definition neg_clique_R (x : fcliques) : R :=
    Some (map sgl__f (flat_map an $x)).

  Lemma neg_clique_R_spec x :
    FAN ⊢ τ (neg_clique_R x) ≡ π x → ⊥o.
  Proof.
    rewrite eo_fan_clique_neg;simpl.
    rewrite map_map.
    apply Join_map_equiv_pointwise.
    intros a ha.
    apply var_clique.
  Qed.
   (* (π x → ⊥o) ⟇ ⋁ (map (fun y => ⋀ (map o_obs ($y − $ x))) l) *)

  Definition implClique (x : fcliques) (y : R) : R :=
    match y with
    | None => None
    | Some yl =>
        orR (neg_clique_R x)
            (fold_right orR (Some [])
                        (map (fun y => fold_right andR None
                                               (map atR ($y−$x)))
                             yl))
    end.

  Lemma τ_Join l :
    FAN ⊢ τ (fold_right orR (Some []) l) ≡ ⋁ (map τ l).
  Proof. induction l;simpl;[|rewrite orR_spec,IHl];reflexivity. Qed.

  Lemma τ_Meet l :
    FAN ⊢ τ (fold_right andR None l) ≡ ⋀ (map τ l).
  Proof. induction l;simpl;[|rewrite andR_spec,IHl];reflexivity. Qed.
  
  Lemma implClique_spec x y :
    FAN ⊢ τ(implClique x y) ≡ π x→τ y.
  Proof.
    destruct y as [yl|].
    - transitivity (τ( orR (neg_clique_R x)
            (fold_right orR (Some [])
                        (map (fun y => fold_right andR None
                                               (map atR ($y−$x)))
                             yl))));[reflexivity|].
      rewrite orR_spec.
      unfold τ at 3; rewrite impl_disj_cliques.
      apply eo_or;[apply neg_clique_R_spec|].
      rewrite τ_Join,map_map.
      apply Join_map_equiv_pointwise.
      intros y hy.
      rewrite τ_Meet,map_map.
      apply Meet_map_equiv_pointwise.
      intros a ha.
      apply atR_spec.
    - simpl.
      symmetry;apply eo_eq_top_iff_top_inf,eo_heyting,eo_inf_top.
  Qed.

  Definition implR (x y : R) : R :=
    match x with
    | None => y
    | Some l => fold_right andR None (map (fun a => implClique a y) l)
    end.

  Lemma implR_spec x y : FAN ⊢ τ(implR x y) ≡ τ x→τ y.
  Proof.
    destruct x.
    - simpl;rewrite τ_Meet,map_map.
      rewrite eo_impl_Join,map_map.
      apply Meet_map_equiv_pointwise.
      intros f hf.
      apply implClique_spec.
    - simpl.
      rewrite eo_top_impl;reflexivity.
  Qed.
      
  Fixpoint nf (s : observation) : R :=
    match s with
    | ⊤o => None
    | ⊥o => Some []
    | ⦑a⦒ => atR a
    | s ⟇ t => orR (nf s) (nf t)
    | s ⟑ t => andR (nf s) (nf t)
    | s → t => implR (nf s) (nf t)
    end.

  Proposition nf_spec s : FAN ⊢ τ (nf s) ≡ s.
  Proof.
    induction s;auto with equiv_obs.
    - simpl;rewrite <- atR_spec;reflexivity.
    - simpl;rewrite orR_spec, IHs1,IHs2;reflexivity.
    - simpl;rewrite andR_spec, IHs1,IHs2;reflexivity.
    - simpl;rewrite implR_spec, IHs1,IHs2;reflexivity.
  Qed.

  Theorem eo_inf_complete :
    (forall l, exists a : vertex, ~ a ∈ l) ->
    forall s t : observation, s ≲ t <-> FAN ⊢ s ≦ t .
  Proof.
    intro h__inf;intros s t;split.
    - pose proof (nf_spec s) as es;pose proof (nf_spec t) as et.
      rewrite <- es,<- et at 2.
      apply (eo_sound FAN_sound) in es,et.
      rewrite <- es,<- et at 1.
      generalize (nf s) (nf t);clear s t es et;intros s t.
      destruct t as [m|];simpl;[|intros;apply eo_inf_top].
      destruct s as [l|];simpl.
      + intros h;unfold__lat.
        cut (! a ⊨ (⋁ (map π l))).
        * intros h';apply h in h'.
          apply satisfies_Join in h' as (x&h'&hx).
          apply in_map_iff in h' as (y&<-&hy).
          eapply π_spec,fc_to_clique_iff,π_proper in hx as ->.
          apply eo_inf_in_Join,in_map_iff;exists y;tauto.
        * apply satisfies_Join;eexists;split;[apply in_map_iff;exists a|];
            eauto.
          apply π_spec;reflexivity.
      + intro f;exfalso.
        destruct (h__inf (flat_map (fun x => $x) m)) as (a&ha);
          apply ha;clear ha.
        cut (sgl a ⊨ (⋁ (map π m))).
        * intro h.
          apply satisfies_Join in h as (b&h1&h2).
          apply in_map_iff in h1 as (x&<-&h1).
          apply π_spec in h2.
          unfold ssmaller in h2.
          setoid_rewrite sgl_spec in h2.
          apply in_flat_map;exists x;split;[assumption|].
          pose proof (@fcliques_non_empty _ _ x) as ne_x.
          case_eq ($x);[tauto|].
          intros b ? e;subst;left;apply h2;simpl.
          apply fc_to_clique_spec;rewrite e;now left.
        * apply f,sat_top;tauto.
    - intros h;apply (eo_sound FAN_sound) in h as <-.
      intro;rsimpl;tauto.
  Qed.

  Theorem eo_inf_dec :
    forall s t : observation, DecidableProp (s ≲ t).
  Proof.
    intros s t.
    case_prop (forall x, x ∈ nf s -> exists y, y ∈ nf t /\ $y ⊆ $x);[left|right].
    - rewrite <-(eo_sound FAN_sound(nf_spec s)).
      rewrite <-(eo_sound FAN_sound(nf_spec t)).
      intros α hx;apply satisfies_Join in hx as (z&hx&hα).
      apply in_map_iff in hx as (x&<-&hx).
      apply hyp in hx as (y&hy&hxy).
      apply fc_to_clique_iff in hxy.
      apply π_spec in hα.
      rewrite <- hxy in hα;rewrite <- hα.
      apply satisfies_Join;eexists;split;[apply in_map_iff;exists y;tauto|].
      apply π_spec;reflexivity.
    - intros f;apply hyp;clear hyp;intros x hx.
      cut (! x ⊨ s).
      + intros h';apply f in h'.
        apply (eo_sound FAN_sound(nf_spec t)),satisfies_Join
          in h' as (yy&e&hxy).
        apply in_map_iff in e as (y&<-&hy).
        exists y;split;[assumption|].
        apply fc_to_clique_iff,π_spec,hxy.
      + apply (eo_sound FAN_sound(nf_spec s)),satisfies_Join.
        exists (π x);split;[apply in_map_iff;exists x;tauto|].
        apply π_spec;reflexivity.
  Qed.
  Corollary eo_ax_complete  :
    forall s t : observation, s ≃ t <-> FAN ⊢ s ≡ t .
  Proof.
    intros s t;split.
    - intros E;apply inf_obs_partialorder;split;apply eo_inf_complete;
        rewrite E;reflexivity.
    - intros E;apply ssmaller_PartialOrder;split;apply eo_inf_complete;
        rewrite E;reflexivity.
  Qed.

  Proposition fan_choose_clique  : choose_clique G.
  Proof.
    intros α s t.
    pose proof (eo_sound FAN_sound(nf_spec s)) as es.
    pose proof (eo_sound FAN_sound(nf_spec t)) as et.
    case_prop
      (exists c, c ∈ (nf s) /\ (forall a, a ∈ $c ->
                               ((a ∝ α) /\ forall b, b ∈ $c -> a ⁐ b))
            /\ forall c', c' ∈ (nf t) -> exists a, a ∈ $c' /\ ~ a ∈ $c /\ ~ a ⊨ α).
    - right.
      setoid_rewrite <- es.
      setoid_rewrite <- et.
      revert hyp;generalize (nf s),(nf t); clear s t es et;intros l m hyp.
      destruct hyp as (γ&h1&h2&h3).
      destruct (decidable_incompatible_with_fcliques α γ).
      * exfalso.
        apply incompatible_incompat in i as (a&ha&hb).
        apply incompat_are_incoh in hb as (b&hb&hab).
        apply fc_to_clique_spec in hb.
        apply h2 in hb as (f1&f2).
        apply hab;symmetry;apply (incompat_None _ f1),ha.
      * apply not_incompatible_is_joins in n as (δ&hδ).
        exists δ;split;[|split].
        -- intros a ha.
           apply hδ;tauto.
        -- apply satisfies_Join;eexists;split.
           ++ apply in_map_iff;eexists;split;[|apply h1].
              reflexivity.
           ++ apply satisfies_Meet;intros x hx.
              apply in_map_iff in hx as (a&<-&ha).
              simpl;apply hδ.
              apply fc_to_clique_spec in ha;tauto.
        -- intros f;apply satisfies_Join in f as (x&hx&f).
           apply in_map_iff in hx as (c'&<-&hc').
           apply h3 in hc' as (a&ha1&ha2&ha3).
           rewrite <- fc_to_clique_spec in ha2.
           apply π_spec in f.
           apply fc_to_clique_spec,f,hδ in ha1;tauto.
    - left.
      setoid_rewrite <- es.
      setoid_rewrite <- et.
      revert hyp;generalize (nf s),(nf t); clear s t es et;intros l m hyp.
      intros β h1 h2.
      apply satisfies_Join in h2 as (x&h&h2).
      apply in_map_iff in h as (c&<-&hc).
      case_prop (exists c', c' ∈ m /\ forall a, a ∈ $c' -> a ⊨ β).
      + destruct hyp0 as (c'&h3&h4).
        apply satisfies_Join;eexists;split.
        * apply in_map_iff;exists c';split;[reflexivity|assumption].
        * apply satisfies_Meet;intros x h.
          apply in_map_iff in h as (a&<-&ha).
          apply h4,ha.
      + exfalso;apply hyp;exists c;split;[assumption|].
        split.
        * intros a ha.
          case_eq (incompat α a).
          -- intros b e; exfalso.
             apply incompat_Some in e as (hb&hab).
             apply hab,(members_are_coh β).
             ++ apply π_spec in h2.
                apply fc_to_clique_spec,h2 in ha.
                apply ha.
             ++ apply h1,hb.
          -- intros h;split;[reflexivity|].
             intros b hb.
             eapply fcliques_coherent;eassumption.
        * intros c' hc'.
          case_prop (exists a, a ∈ $ c' /\ ~ a ∈ $ c /\ ~ a ⊨ α);[tauto|].
          exfalso.
          apply hyp0;exists c';split;[assumption|].
          intros a ha.
          apply π_spec in h2.
          case_in a ($c).
          -- apply h2,fc_to_clique_spec,I. 
          -- apply h1.
             case_prop(a⊨ α);[assumption|].
             exfalso;apply hyp1;exists a;tauto.
  Qed.

  Fixpoint finsat (x : fcliques) s :=
    match s with
    | ⊤o  => True
    | ⊥o => False
    | ⦑u⦒ => u ∈ $ x
    | o1 ⟇ o2 => finsat x o1 \/ finsat x o2
    | o1 ⟑ o2 => finsat x o1 /\ finsat x o2
    | o1 → o2 => forall y, finsat y o1 -> $x ⊆ $y -> finsat y o2
    end.

  Lemma finsat_spec x s : finsat x s <-> !x ⊨ s.
  Proof.
    revert x;induction s;intro x;simpl; rsimpl;try tauto.
    - rewrite fc_to_clique_spec;reflexivity.
    - rewrite IHs1,IHs2;reflexivity.
    - rewrite IHs1,IHs2;reflexivity.
    - split;intros h y h1 h2.
      + cut (exists z, ! z ≲ y /\ !x ≲ !z /\ !z ⊨ s1).
        * intros (z&hzy&hxz&hz).
          rewrite <- hzy.
          apply IHs2,h,fc_to_clique_iff,hxz.
          apply IHs1,hz.
        * pose proof (eo_sound FAN_sound(nf_spec s1)) as e.
          apply e,satisfies_Join in h1 as (zz&hzz&hz).
          apply in_map_iff in hzz as (z'&<-&hz').          
          apply π_spec in hz.
          destruct (incompatible_or_joins_f x z')
            as [(a&b&ha&hb&hab)|(z&jz)].
          -- exfalso.
             apply fc_to_clique_spec,hz in hb.
             apply fc_to_clique_spec,h2 in ha.
             apply hab,(members_are_coh y);assumption.
          -- exists z.
             pose proof jz as ez.
             apply joins_is_meet_f in jz as (hz1&hz2&hz3).
             repeat split.
             ++ intros a;rewrite fc_to_clique_spec,(ez a).
                rewrite in_app_iff;intros [ha|ha];
                  [apply h2|apply hz];apply fc_to_clique_spec,ha.
             ++ apply fc_to_clique_iff,hz1.
             ++ apply fc_to_clique_iff in hz2 as <-.
                apply e,satisfies_Join;eexists;split;
                  [apply in_map_iff;exists z';tauto|].
                apply π_spec;reflexivity.
      + apply IHs2,h,fc_to_clique_iff,h2.
        apply IHs1,h1.
  Qed.

  Lemma sat_iff_inf_finsat α s : α ⊨ s <-> exists x, α ⊃ ! x /\ finsat x s.
  Proof.
    setoid_rewrite finsat_spec.
    split;[|intros (x&<-&h);apply h].
    intros h.
    pose proof (eo_sound FAN_sound(nf_spec s)) as e.
    apply e,satisfies_Join in h as (z&hz&hx1).
    apply in_map_iff in hz as (x&<-&hx2).
    exists x;split.
    - apply π_spec,hx1.
    - apply e,satisfies_Join;exists (π x);split.
      + apply in_map_iff;exists x;tauto.
      + apply π_spec;reflexivity.
  Qed.
End s.
