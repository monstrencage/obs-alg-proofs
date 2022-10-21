(** * Anticlique graph : an infinite graph with no edge *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Import equiv_obs sem_obs.
Require Import laws.


Section s.
  Context {V : Set} {decV : decidable_set V}.
  Hypothesis infiniteV : forall l : list V, exists a : V, ~ a ∈ l.
  Context { a__o : V}.

  (** * Definition of the graph *)
  Instance Ω : Graph := 
    {
    vertex := V;
    coh := @eq V;
    coh_refl := @eq_Reflexive V;
    coh_sym := @eq_Symmetric V
    }.

  Instance decΩ : DecidableGraph Ω.
  Proof.
    split.
    - exact decV.
    - intros;apply DecidableProp_Eq,decV.
  Qed.

  (** * Axiomatisation *)
  Reserved Notation " x =Ω y " (at level 80).
  Inductive Ω_ax : relation observation :=
  | Ω_top' a b : ⦑a⦒⟇(⦑a⦒→⊥o) =Ω ⦑b⦒⟇(⦑b⦒→⊥o)
  | Ω_neg (X : list V) : ((⋁ (map o_obs X))→⊥o)→⊥o =Ω ⋁ (map o_obs X)
  where " x =Ω y " := (Ω_ax x y).
  Notation axΩ := (ha_ax (+) (obs_ax (+) Ω_ax)).
  Hint Constructors Ω_ax : core.

  Remark eo_Ω_top' a b : axΩ ⊢ ⦑a⦒⟇(⦑a⦒→⊥o) ≡ ⦑b⦒⟇(⦑b⦒→⊥o).
  Proof. auto with equiv_obs. Qed.
  Remark eo_Ω_neg X : axΩ ⊢ ((⋁ (map o_obs X))→⊥o)→⊥o ≡ ⋁ (map o_obs X).
  Proof. auto with equiv_obs. Qed.

  (** * Basic laws *)
  Notation "⊤'" := (⦑ a__o ⦒ ⟇ (⦑ a__o ⦒→⊥o)).

  Lemma top'_a a : axΩ ⊢ ⦑a⦒ ≦ ⊤'.
  Proof.
    transitivity (⦑ a ⦒⟇(⦑ a ⦒ → ⊥o));
      [apply eo_inf_or_left;reflexivity|].
    erewrite eo_Ω_top';reflexivity. 
  Qed.

  Lemma top'_not_a a : axΩ ⊢ ⦑a⦒ → ⊥o ≦ ⊤'.
  Proof.
    transitivity (⦑ a ⦒⟇(⦑ a ⦒ → ⊥o));
      [apply eo_inf_or_right;reflexivity|].
    erewrite eo_Ω_top';reflexivity. 
  Qed.

  Lemma top'_or_neg a b :
    a <> b -> axΩ ⊢ ⊤' ≦ (⦑ a ⦒ → ⊥o) ⟇ (⦑ b ⦒ → ⊥o).
  Proof.
    intros h.
    rewrite (eo_Ω_top' a__o a).
    unfold__lat.
    - apply eo_inf_or_right,eo_heyting.
      rewrite<- eo_eq_bot_iff_inf_bot.
      auto with equiv_obs.
    - apply eo_inf_or_left;reflexivity.
  Qed.
   Lemma neg_neg_axΩ a : axΩ ⊢ (⦑a⦒ → ⊥o)→ ⊥o ≡ ⦑a⦒.
  Proof.
    transitivity (⋁(map o_obs [a]));[|simpl;apply eo_or_bot].
    rewrite <- eo_Ω_neg.
    apply eo_impl;[|reflexivity].
    apply eo_impl;[|reflexivity].
    simpl;symmetry;apply eo_or_bot.
  Qed.

  Lemma neg_top'_is_bot :
    axΩ ⊢ ⊤' → ⊥o ≡ ⊥o.
  Proof. rewrite eo_impl_distr_left;apply eo_contradict. Qed.

  Lemma weak_excluded_middle u :
    axΩ ⊢ ⊤' ≦ ⋁ (map o_obs u) ⟇ (⋁ (map o_obs u) → ⊥o).
  Proof.
    rewrite eo_impl_Join,or_Meet,map_map.
    apply obs_Meet;intros x hx;apply in_map_iff in hx as (y&<-&hy).
    apply in_map_iff in hy as (a&<-&ha).
    rewrite (eo_Ω_top' _ a).
    apply o_or_inf;[apply eo_inf_in_Join,in_map_iff;exists a;tauto
                   |reflexivity].
  Qed.

  Remark Meet_not_and_sgl_not_in x u :
    ~ x ∈ u -> axΩ ⊢ ⋀ (map (fun a => ⦑ a ⦒ → ⊥o) u) ⟑ ⦑ x ⦒ ≡ ⦑ x ⦒.
  Proof.
    intro h.
    rewrite eo_and_comm,<- eo_inf_o_and.
    apply obs_Meet.
    intros y hy;apply in_map_iff in hy as (a&<-&ha).
    apply eo_heyting.
    rewrite <- eo_eq_bot_iff_inf_bot.
    cut (x ⌣ a);[auto with equiv_obs|intros <-].
    tauto.
  Qed.
  
  Remark Meet_not_and_sgl_in x u :
    x ∈ u ->
    axΩ ⊢ ⋀ (map (fun a : V => ⦑ a ⦒ → ⊥o) u) ⟑ ⦑ x ⦒ ≡ ⊥o.
  Proof.
    intro h.
    split_order;[|apply eo_inf_bot].
    rewrite eo_and_comm.
    etransitivity;[|eapply eq_obs_inf_obs,eo_contradict].
    apply o_and_inf;[reflexivity|].
    apply eo_inf_in_Meet,in_map_iff;exists x;tauto.
  Qed.

  (** * Representations *)
  Definition Obs__Ω := option (list V + list V)%type.
  Definition V' := option V.

  Instance sat__Ω : Satisfaction V' Obs__Ω :=
    fun x (o : Obs__Ω) =>
      match x,o with
      | _,None => True
      | Some a,Some (inl u) => ~ a ∈ u
      | Some a,Some (inr u) => a ∈ u
      | _,_ => False
      end.
  
  Definition inf__Ω : Obs__Ω -> Obs__Ω -> bool :=
    fun x y =>
      match x,y with
      | _,None => true
      | Some(inl u),Some(inl v)
      | Some(inr v),Some(inr u) => inclb v u
      | Some(inr u),Some(inl v) => (u ∩ v) =?= []
      | _,_ => false
      end.
  
  Lemma complete_inf__Ω s t : inf__Ω s t = true <-> s ≲ t.
  Proof.
    destruct s as [[u|u]|], t as [[v|v]|];simpl;try tauto.
    - rewrite inclb_correct;split.
      + intros h [a|];unfold satisfies;simpl;[pose proof (h a)|];tauto.
      + intros h a ha.
        case_in a u;[tauto|].
        exfalso;apply (h (Some a)).
        * apply I.
        * apply ha.
    - split;[discriminate|].
      intro f;exfalso.
      destruct (infiniteV (u++v)) as [a ha].
      rewrite in_app_iff in ha.
      case_in a u;[tauto|].
      apply (f (Some a)) in I;apply ha;right;apply I.
    - split;[intros _|reflexivity].
      intros [] _;exact I.
    - rewrite eqX_correct;split.
      + intros e [a|] ha;unfold satisfies in *;simpl in *.
        * intros f;cut (a ∈ []);[simpl;tauto|].
          rewrite <-e ;apply intersect_spec;tauto.
        * tauto.
      + intros h;apply incl_l_nil.
        intros a ha;apply intersect_spec in ha as (hu&hv);simpl.
        revert hv;apply (h (Some a)),hu.
    - rewrite inclb_correct;split.
      + intros h [a|];unfold satisfies;simpl;[pose proof (h a)|];tauto.
      + intros h a ha.
        apply (h (Some a)),ha.
    - split;[intros _|reflexivity].
      intros [] _;exact I.
    - split;[discriminate|].
      intros f;exfalso;apply (f None),I.
    - split;[discriminate|].
      intros f;exfalso;apply (f None),I.
    - split;reflexivity. 
  Qed.

  (** * Cliques are either empty or singletons *)
  Remark cliques_at_most_one_elt α a b :
    a ∊ α -> b ∊ α -> a = b.
  Proof. apply (members_are_coh α). Qed.
  
  Corollary mem_is_sgl α a : a ⊨ α <-> α ≃ sgl a.
  Proof.
    split;[|intros e;apply e,sgl_spec;reflexivity].
    intros h1 b.
    unfold satisfies,satClique at 1;simpl.
    unfold satClique.
    rewrite (sgl_spec b a).
    split.
    - intros h2;eapply cliques_at_most_one_elt;assumption.
    - intros ->;assumption.
  Qed.

  (** * Isomorphism between cliques and [option V] *)
  Definition ξ : V' -> clique :=
    fun x => match x with None => empt | Some a => sgl a end.

  Definition ζ : clique -> V' :=
    fun α =>
      match (incompat α a__o) with
      | Some a => Some a
      | None => if member α a__o then Some a__o else None
      end.

  Lemma ζ_Some α a : ζ α = Some a -> α ≃ sgl a.
  Proof.
    unfold ζ;case_eq (incompat α a__o).
    - intros b eb e;inversion e;subst.
      apply incompat_Some in eb.
      apply mem_is_sgl,eb.
    - intros h;case_eq (member α a__o);[|discriminate].
      intros ea e;inversion e;subst.
      apply mem_is_sgl,Is_true_eq_left,ea.
  Qed.

  Lemma ζ_None α : ζ α = None -> α ≃ empt.
  Proof.
    unfold ζ;case_eq (incompat α a__o);[discriminate|].
    intros h;case_eq (member α a__o);[discriminate|].
    rewrite <-not_true_iff_false,<-Is_true_iff_eq_true.
    intros h' _ a;split;[|intro f;exfalso;apply f].
    intros e;apply mem_is_sgl in e;apply h',e,sgl_spec.
    apply (incompat_None _ h),e,sgl_spec;reflexivity.
  Qed.

  Corollary ξ_ζ α : ξ (ζ α) ≃ α.
  Proof. symmetry;case_eq (ζ α);[apply ζ_Some|apply ζ_None]. Qed.
  
  Lemma ζ_sgl a : ζ (sgl a) = Some a.
  Proof. 
    unfold ζ;case_eq (incompat (!(@sgl__f Ω _ a)) a__o).
    - intros b eb;f_equal.
      apply sgl_spec.
      eapply incompat_Some,eb.
    - intros h;case_eq (member (!(@sgl__f Ω _ a)) a__o).
      + intro e;apply Is_true_iff_eq_true,sgl_spec in e as ->.
        reflexivity.
      + rewrite <-not_true_iff_false,<-Is_true_iff_eq_true.
        intros f;exfalso.
        destruct_eqX a__o a.
        * apply f,sgl_spec;reflexivity.
        * apply N,(incompat_None _ h),sgl_spec;reflexivity. 
  Qed.
  
  Lemma ζ_empt : ζ empt = None.
  Proof.  reflexivity. Qed.
  
  Corollary ζ_ξ x : ζ(ξ x) = x.
  Proof. destruct x as [a|];[apply ζ_sgl|apply ζ_empt]. Qed.

  (** * The axioms are sound *)
  Proposition axΩ_sound : subrelation axΩ sequiv.
  Proof.
    intros _ _ [s t h|_ _ [s t h|_ _ [a b|X]]]. 
    - apply ha_sound,h.
    - apply Obs_sound,jright,h.
    - destruct_eqX a b;[reflexivity|].
      intro α.
      rewrite <- (ξ_ζ α);rsimpl.
      setoid_rewrite sat_at.
      setoid_rewrite sat_bot.
      destruct (ζ α) as [c|].
      + simpl;setoid_rewrite sgl_spec.
        split;intros _;[destruct_eqX b c|destruct_eqX a c];
          (now left)||right;intros y hy;apply mem_is_sgl in hy as ->.
        * intros f;apply N0,symmetry;apply sgl_spec,f,sgl_spec.
          reflexivity.
        * intros f;apply N0,symmetry;apply sgl_spec,f,sgl_spec.
          reflexivity.
      + unfold satisfies at 1 3,satClique;simpl.
        split;(intros [h|h];exfalso;[apply h|]);
          [apply (h(sgl a))|apply (h (sgl b))];
          (apply sgl_spec;reflexivity)||apply (@empt_max Ω).
    - intros α;rsimpl.
      setoid_rewrite sat_bot.
      rewrite satisfies_Join.
      setoid_rewrite sat_impl.
      setoid_rewrite satisfies_Join.
      setoid_rewrite in_map_iff.
      setoid_rewrite sat_bot.
      split.
      + pose proof (ξ_ζ α) as e;setoid_rewrite <- e.
        destruct (ζ α) as [a|];simpl.
        * intros h.
          case_in a X.
          -- eexists ;split.
             ++ exists a;tauto.
             ++ apply sat_at,sgl_spec;reflexivity.
          -- exfalso;apply (h (!(@sgl__f Ω _ a)));[|reflexivity].
             intros y (x&(b&<-&hb)&e').
             apply sat_at,mem_is_sgl in e' as ->.
             intros f;destruct_eqX a b;[tauto|].
             apply N,(@sgl_spec Ω _ a b),f,sgl_spec;reflexivity.
        * destruct(infiniteV X) as [a ha].
          intros h;exfalso;apply (h (!(@sgl__f Ω _ a)));
            [|apply (@empt_max Ω)].
          intros y (x&(b&<-&hb)&e').
          apply sat_at,mem_is_sgl in e' as ->.
          intros f;destruct_eqX a b;[tauto|].
          apply N,(@sgl_spec Ω _ a b),f,sgl_spec;reflexivity.
      + intros (x&(a&<-&ha)&e);apply mem_is_sgl in e.
        setoid_rewrite e.
        intros y h1 h2.
        apply (h1 (!(@sgl__f Ω _ a))).
        * eexists;split;[exists a;tauto|].
          apply sat_at,sgl_spec;reflexivity.
        * intros b hb.
          apply sgl_spec;symmetry;apply sgl_spec.
          apply mem_is_sgl in hb.
          apply hb,h2,sgl_spec;reflexivity.
  Qed.

  Corollary inf_axΩ_sound s t :
    axΩ ⊢ s ≦ t -> s ≲ t.
  Proof.
    intro h;apply eo_sound in h as <-;[|apply axΩ_sound].
    intro;rsimpl;tauto.
  Qed.
  Corollary eq_axΩ_sound s t :
    axΩ ⊢ s ≡ t -> s ≃ t.
  Proof.
    intro h;apply eo_sound in h as <-;[|apply axΩ_sound].
    intro;simpl;tauto.
  Qed.

  (** * From representations to terms *)
  Definition τ (o : Obs__Ω) : observation :=
    match o with
    | None => ⊤o
    | Some (inl u) =>
      if u =?= []
      then ⊤'
      else ⋀ (map (fun a => ⦑ a ⦒ → ⊥o) u)
    | Some (inr u) => ⋁ (map o_obs u)
    end.

  Lemma τ_ζ α o : α ⊨ (τ o) -> ζ α ⊨ o.
  Proof.
    case_eq (ζ α).
    - intros a ea;apply ζ_Some in ea as ->.
      unfold satisfies at 2.
      destruct o as [[u|u]|];simpl. 
      + destruct_eqX u (@nil V).
        * simpl;tauto.
        * intros h1 h2.
          cut (@satisfies _ _ satObs_SatRel (sgl a) (⦑a⦒→⊥o)).
          -- rsimpl;intros f.
             cut (@satisfies _ _ satObs_SatRel (sgl a) ⊥o).
             ++ rsimpl;tauto.
             ++ apply f;[simpl;apply sgl_spec|];reflexivity.
          -- rewrite satisfies_Meet in h1.
             apply h1,in_map_iff;exists a;tauto.
      + intros h;apply satisfies_Join in h as (x&hx&h).
        apply in_map_iff in hx as (b&<-&hb);rsimpl in *.
        apply sgl_spec in h;subst;tauto.
      + tauto.
    - intro h;apply ζ_None in h as ->.
      unfold satisfies at 2.
      destruct o as [[u|u]|];simpl;[| |intro h;apply h];intro f;exfalso.
      + destruct_eqX u (@nil V).
        * destruct f as [f|f];simpl in f.
          -- tauto.
          -- apply (f (!(@sgl__f Ω _ a__o))).
             ++ apply sgl_spec;reflexivity.
             ++ apply (empt_max (!(@sgl__f Ω _ a__o))).
        * destruct u as [|a u];[tauto|cut (empt ⊨ (⦑a⦒→⊥o))].
          -- rsimpl.
             setoid_rewrite sat_at.
             setoid_rewrite sat_bot.
             intro ff.
             apply (ff (!(@sgl__f Ω _ a))).
             ++ apply sgl_spec;reflexivity.
             ++ apply (@empt_max Ω).
          -- apply f.
      + apply satisfies_Join in f as (x&hx&h).
        apply in_map_iff in hx as (a&<-&ha).
        apply h.
  Qed.

  Lemma τ_ξ α o : α ⊨ o -> ξ α ⊨ (τ o).
  Proof.
    unfold satisfies at 1,sat__Ω; destruct o as [[u|u]|],α as [b|];simpl;
      rsimpl;try tauto.
    - destruct_eqX u (@nil V);simpl.
      + intros _;rsimpl.
        destruct_eqX b a__o.
        * left;apply sgl_spec;reflexivity.
        * right.
          intros y h1 h2;rsimpl in *.
          apply mem_is_sgl in h1.
          rewrite h1 in h2.
          apply N.
          apply (@sgl_spec Ω _ b a__o),h2,sgl_spec;reflexivity.
      + intros hv;rewrite satisfies_Meet.
        intros x hx;apply in_map_iff in hx as (a&<-&ha).
        rsimpl;intros y h1 h2;rsimpl in *.
        apply mem_is_sgl in h1.
        rewrite h1 in h2.
        replace a with b in *;[tauto|].
        apply (@sgl_spec Ω _ b a),h2,sgl_spec;reflexivity.
    - intro h;apply satisfies_Join;eexists;split.
      + apply in_map_iff;exists b;split;[reflexivity|assumption].
      + apply sat_at,sgl_spec;reflexivity.
  Qed.

  Lemma sound_τ_sat__Ω α o : α ⊨ (τ o) <-> ζ α ⊨ o.
  Proof.
    split;[apply τ_ζ|].
    rewrite <- (ξ_ζ α) at 2.
    apply τ_ξ.
  Qed.
  
  Instance τ_proper_inf__Ω : Proper (ssmaller ==> inf_obs axΩ) τ.
  Proof.
    intros u v; rewrite <- complete_inf__Ω.
    destruct u as [[u|u]|], v as [[v|v]|];simpl;
      try discriminate||rewrite inclb_correct||rewrite eqX_correct;
      intros hyp.
    - destruct_eqX u (@nil V);destruct_eqX v (@nil V).
      + reflexivity.
      + exfalso.
        apply incl_l_nil in hyp as ->;tauto.
      + destruct u as [|a u];[tauto|].
        apply eo_inf_and_left,top'_not_a.
      + unfold__lat.
        apply eo_inf_in_Meet,in_map_iff;exists a;split;[reflexivity|].
        apply hyp,ha.
    - apply eo_inf_top.
    - unfold__lat.
      destruct_eqX v (@nil V).
      + apply top'_a.
      + unfold__lat.
        rewrite <-eo_heyting,<-eo_eq_bot_iff_inf_bot.
        apply eo_ax,jright,jleft,obs_incoh.
        intros <-;cut (a ∈ (u∩v));[rewrite hyp;simpl
                                 |apply intersect_spec];
          tauto.
    - unfold__lat.
      apply eo_inf_in_Join,in_map_iff;exists a;split;
        [reflexivity|apply hyp,ha].
    - apply eo_inf_top.
    - reflexivity.
  Qed. 

  Instance dec_inf__Ω x y : DecidableProp (x ≲ y).
  Proof.
    case_eq (inf__Ω x  y);intro e;[left|right];
      rewrite <-complete_inf__Ω,e;[reflexivity|discriminate].
  Qed.

  (** * From terms to reprentations *)
  Fixpoint to_Obs__Ω s : Obs__Ω :=
    match s with
    | ⊥o => Some (inr [])
    | ⊤o => None
    | ⦑a⦒ => Some (inr [a])
    | s⟇t => match (to_Obs__Ω s),(to_Obs__Ω t) with
            | None,_ | _,None => None
            | Some(inl u),Some(inl v) => Some(inl (u∩v))
            | Some(inr u),Some(inr v) => Some(inr (u++v))
            | Some(inl u),Some(inr v)
            | Some(inr v),Some(inl u) => Some(inl (u−v))
            end
    | s⟑t => match (to_Obs__Ω s),(to_Obs__Ω t) with 
    | Some(inl u),Some(inl v) => Some(inl (u++v))
    | Some(inr u),Some(inr v) => Some(inr (u∩v))
    | Some(inl u),Some(inr v)
    | Some(inr v),Some(inl u) => Some(inr (v−u))
    | None,z | z,None => z
    end
    | s→t =>
        if inf__Ω (to_Obs__Ω s) (to_Obs__Ω t)
        then None
        else
          match (to_Obs__Ω s),(to_Obs__Ω t) with
          | x,None | None,x => x
          | Some (inl u),Some (inl v) => Some (inl (v − u))
          | Some (inr u),Some (inl v) => Some (inl (u ∩ v))
          | Some (inl u),Some (inr v) => Some (inr (u ++ v))
          | Some (inr u),Some (inr v) => Some (inl (u − v))
          end
    end.

  Lemma τ_join__Ω s t :
    axΩ ⊢ τ (to_Obs__Ω (s ⟇ t)) ≡ τ (to_Obs__Ω s) ⟇ τ (to_Obs__Ω t).
  Proof.
    simpl;destruct (to_Obs__Ω s) as [[u|u]|],
        (to_Obs__Ω t) as [[v|v]|];simpl.
    - destruct_eqX (u∩v) (@nil V).
      + destruct_eqX u (@nil V);destruct_eqX v (@nil V).
        * symmetry;apply eo_or_idem.
        * split_order;[apply eo_inf_or_left;reflexivity|].
          apply obs_join;[reflexivity|].
          destruct v;[tauto|apply eo_inf_and_left].
          apply top'_not_a.
        * split_order;[apply eo_inf_or_right;reflexivity|].
          apply obs_join;[|reflexivity].
          destruct u;[tauto|apply eo_inf_and_left].
          apply top'_not_a.
        * split_order.
          -- rewrite (Meet_or_Meet (map _ u) (map _ v)).
             unfold_meet.
             destruct a as (a1&a2).
             apply pairs_spec in ha as (h1&h2).
             apply in_map_iff in h1 as (a&<-&ha).
             apply in_map_iff in h2 as (b&<-&hb);simpl.
             apply top'_or_neg.
             intros ->.
             cut (b ∈ []);[simpl;tauto|].
             rewrite <-E,intersect_spec;tauto.
          -- unfold__lat.
             ++ destruct u as [|a u];[tauto|simpl].
                apply eo_inf_and_left.
                apply top'_not_a.
             ++ destruct v as [|a v];[tauto|simpl].
                apply eo_inf_and_left.
                apply top'_not_a.
      + destruct_eqX u (@nil V);destruct_eqX v (@nil V);simpl in *;
          try tauto.
        * exfalso;apply N,incl_l_nil;intro.
          rewrite intersect_spec;simpl;tauto.
        * split_order.
          -- rewrite Meet_or_Meet.
             unfold__lat.
             destruct a as (?&?);apply pairs_spec in ha as (h1&h2).
             apply in_map_iff in h1 as (a&<-&ha).
             apply in_map_iff in h2 as (b&<-&hb);simpl.
             destruct_eqX a b.
             ++ apply eo_inf_or_left,eo_inf_in_Meet,in_map_iff.
                exists b;split;[reflexivity|].
                apply intersect_spec;tauto.
             ++ etransitivity;[clear a b ha hb N2 N0 N1
                              |apply (top'_or_neg N2)].
                destruct (u∩v) as [|a uv];[tauto|simpl].
                apply eo_inf_and_left,top'_not_a.
          -- unfold__lat;apply eo_inf_in_Meet,in_map_iff;
               apply intersect_spec in ha as (h1&h2);exists a;tauto.
    - destruct_eqX u (@nil V);[|destruct_eqX (u − v) (@nil V)].
      + split_order.
        * apply eo_inf_or_left;reflexivity.
        * unfold__lat;apply top'_a||apply top'_not_a.
      + split_order;[|unfold__lat].
        * rewrite (eo_or_comm (⋀ (map _ u)) (⋁ (map _ v))).
          rewrite or_Meet,map_map.
          unfold_meet.
          rewrite (eo_Ω_top' a__o a);apply obs_join.
          -- apply eo_inf_or_left,eo_inf_in_Join,in_map_iff.
             exists a;split;[reflexivity|].
             case_in a v;[tauto|].
             exfalso;cut (a ∈ []);[simpl;tauto|].
             rewrite <- E;apply difference_spec;tauto.
          -- apply eo_inf_or_right;reflexivity.
        * destruct u as [|a u];[tauto|simpl].
          apply eo_inf_and_left,top'_not_a.
        * apply top'_a.
      + split_order;[rewrite eo_or_comm,or_Meet,map_map|]; unfold__lat.
        * case_in a v.
          -- transitivity ⊤'.
             ++ destruct (u−v) as [|b uv];[tauto|simpl].
                apply eo_inf_and_left,top'_not_a.
             ++ rewrite (eo_Ω_top' a__o a);unfold__lat.
                ** apply eo_inf_or_left,eo_inf_in_Join,in_map_iff.
                   exists a;tauto.
                ** apply eo_inf_or_right;reflexivity.
          -- apply eo_inf_or_right,eo_inf_in_Meet,in_map_iff.
             exists a;split;[reflexivity|].
             apply difference_spec;tauto.
        * apply eo_inf_in_Meet,in_map_iff.
          exists a;apply difference_spec in ha;tauto.
        * apply eo_heyting.
          rewrite <- eo_eq_bot_iff_inf_bot.
          cut (a ⌣ a0);[auto with equiv_obs|intros <-].
          apply difference_spec in ha0;tauto.
    - symmetry;apply eo_or_top.
    - destruct_eqX v (@nil V);[|destruct_eqX (v − u) (@nil V)].
      + split_order.
        * apply eo_inf_or_right;reflexivity.
        * unfold__lat;apply top'_a||apply top'_not_a.
      + split_order;[|unfold__lat].
        * rewrite or_Meet,map_map.
          unfold_meet.
          rewrite (eo_Ω_top' a__o a);apply obs_join.
          -- apply eo_inf_or_left,eo_inf_in_Join,in_map_iff.
             exists a;split;[reflexivity|].
             case_in a u;[tauto|].
             exfalso;cut (a ∈ []);[simpl;tauto|].
             rewrite <- E;apply difference_spec;tauto.
          -- apply eo_inf_or_right;reflexivity.
        * apply top'_a.
        * destruct v as [|a v];[tauto|simpl].
          apply eo_inf_and_left,top'_not_a.
      + split_order;[rewrite or_Meet,map_map|];unfold__lat.
        * case_in a u.
          -- transitivity ⊤'.
             ++ destruct (v−u) as [|b uv];[tauto|simpl].
                apply eo_inf_and_left,top'_not_a.
             ++ rewrite (eo_Ω_top' a__o a);unfold__lat.
                ** apply eo_inf_or_left,eo_inf_in_Join,in_map_iff.
                   exists a;tauto.
                ** apply eo_inf_or_right;reflexivity.
          -- apply eo_inf_or_right,eo_inf_in_Meet,in_map_iff.
             exists a;split;[reflexivity|].
             apply difference_spec;tauto.
        * apply eo_heyting.
          rewrite <- eo_eq_bot_iff_inf_bot.
          cut (a ⌣ a0);[auto with equiv_obs|intros <-].
          apply difference_spec in ha0;tauto.
        * apply eo_inf_in_Meet,in_map_iff.
          exists a;apply difference_spec in ha;tauto.
    - rewrite map_app;apply Join_app.
    - symmetry;apply eo_or_top.
    - symmetry;etransitivity;[apply eo_or_comm|apply eo_or_top].
    - symmetry;etransitivity;[apply eo_or_comm|apply eo_or_top].
    - symmetry;apply eo_or_top.
  Qed.
      
  Lemma τ_meet__Ω s t :
    axΩ ⊢ τ (to_Obs__Ω (s ⟑ t)) ≡ τ (to_Obs__Ω s) ⟑ τ (to_Obs__Ω t).
  Proof.
    simpl;destruct (to_Obs__Ω s) as [[u|u]|],(to_Obs__Ω t) as [[v|v]|];simpl.
    - destruct_eqX (u++v) (@nil V).
      + apply app_eq_nil in E as (->&->);rewrite eqX_refl.
        symmetry;apply eo_and_idem.
      + destruct_eqX u (@nil V);
          destruct_eqX v (@nil V);[subst;simpl in *;tauto| | |].
        * simpl in *.
          symmetry;rewrite eo_and_comm.
          apply eo_inf_o_and.
          destruct v as [|a v];[tauto|simpl].
          apply eo_inf_and_left,top'_not_a.
        * rewrite app_nil_r in *.
          symmetry;apply eo_inf_o_and.
          destruct u as [|a u];[tauto|simpl].
          apply eo_inf_and_left,top'_not_a.
        * rewrite map_app;apply Meet_app.
    - destruct_eqX u (@nil V).
      + replace (v − []) with v by
            (clear;induction v;simpl;[|rewrite <- IHv];reflexivity).
        symmetry;rewrite eo_and_comm.
        apply eo_inf_o_and.
        unfold_join;apply top'_a.
      + rewrite and_Join,map_map.
        split_order;unfold__lat.
        * apply difference_spec in ha as (ha1&ha2).
          etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;split;
                          [reflexivity|assumption]].
          unfold__lat;[|reflexivity].
          apply eo_heyting;rewrite <- eo_eq_bot_iff_inf_bot.
          cut (a ⌣ a0);[auto with equiv_obs|intros <-].
          tauto.
        * case_in a u.
          -- etransitivity;[|apply eo_inf_bot].
             etransitivity;[apply o_and_inf;
                            [apply eo_inf_in_Meet,in_map_iff;
                             exists a;tauto
                            |reflexivity]|].
             apply eo_heyting;reflexivity.
          -- apply eo_inf_and_right,eo_inf_in_Join,in_map_iff.
             exists a;split;[reflexivity|].
             apply difference_spec;tauto.
    - symmetry;apply eo_and_top.
    - destruct_eqX v (@nil V).
      + replace (u − []) with u by
            (clear;induction u;simpl;[|rewrite <- IHu];reflexivity).
        symmetry;apply eo_inf_o_and.
        unfold_join;apply top'_a.
      + rewrite eo_and_comm.
        rewrite and_Join,map_map.
        split_order;unfold__lat.
        * apply difference_spec in ha as (ha1&ha2).
          etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;split;
                          [reflexivity|assumption]].
          unfold__lat;[|reflexivity].
          apply eo_heyting;rewrite <- eo_eq_bot_iff_inf_bot.
          cut (a ⌣ a0);[auto with equiv_obs|intros <-].
          tauto.
        * case_in a v.
          -- etransitivity;[|apply eo_inf_bot].
             etransitivity;[apply o_and_inf;
                            [apply eo_inf_in_Meet,in_map_iff;
                             exists a;tauto
                            |reflexivity]|].
             apply eo_heyting;reflexivity.
          -- apply eo_inf_and_right,eo_inf_in_Join,in_map_iff.
             exists a;split;[reflexivity|].
             apply difference_spec;tauto.
    - split_order.
      + unfold__lat;apply intersect_spec in ha as (hau&hav);
          apply eo_inf_in_Join,in_map_iff;exists a;tauto.
      + rewrite Join_and_Join.
        unfold__lat.
        destruct a as [a1 a2];apply pairs_spec in ha as (ha&hb);
          apply in_map_iff in ha as (a&<-&ha);
          apply in_map_iff in hb as (b&<-&hb);simpl.
        destruct_eqX a b.
        * apply eo_inf_and_left,eo_inf_in_Join,in_map_iff.
          exists b;rewrite intersect_spec;tauto.
        * etransitivity;[|apply eo_inf_bot].
          rewrite <- eo_eq_bot_iff_inf_bot.
          auto with equiv_obs.          
    - symmetry;apply eo_and_top.
    - symmetry;etransitivity;[apply eo_and_comm|apply eo_and_top].
    - symmetry;etransitivity;[apply eo_and_comm|apply eo_and_top].
    - symmetry;apply eo_and_idem.
  Qed.
  
  Lemma τ_neg__Ω s : axΩ ⊢ τ (to_Obs__Ω (s→⊥o)) ≡ τ (to_Obs__Ω s) → ⊥o.
  Proof.
    simpl;destruct (to_Obs__Ω s) as [[u|u]|];simpl.
    - destruct_eqX u (@nil V);simpl.
      + rewrite eo_impl_distr_left.
        rewrite neg_neg_axΩ,eo_and_comm,eo_contradict;reflexivity.
      + rewrite app_nil_r,<- (eo_Ω_neg u) at 1.
        apply eo_impl;[|reflexivity].
        etransitivity;[apply eo_impl_Join|].
        rewrite map_map;reflexivity.
    - destruct_eqX u (@nil V);simpl.
      + symmetry;apply eo_tauto.
      + case_eq (inclb u (@nil V)).
        * rewrite inclb_correct;intro f;exfalso;apply N,incl_l_nil,f.
        * intros _.
          rewrite difference_nil;simpl.
          replace (u =?= []) with false by (symmetry;apply eqX_false,N).
          symmetry;etransitivity;[apply eo_impl_Join|].
          rewrite map_map;reflexivity.
    - symmetry;etransitivity;[symmetry;apply eo_and_top|].
      apply eo_eq_bot_iff_inf_bot.
      apply eo_heyting;reflexivity.
  Qed.
  
  Lemma τ_impl__Ω s t :
    axΩ ⊢ τ (to_Obs__Ω (s → t)) ≡ τ (to_Obs__Ω s) → τ (to_Obs__Ω t).
  Proof.
    simpl;case_eq (inf__Ω (to_Obs__Ω s)(to_Obs__Ω t)).
    - intros h;apply complete_inf__Ω in h.
      simpl;symmetry.
      apply eo_eq_top_iff_top_inf,eo_heyting.
      rewrite eo_and_comm,eo_and_top.
      apply τ_proper_inf__Ω,h.
    - destruct (to_Obs__Ω s) as [[u|u]|],(to_Obs__Ω t) as [[v|v]|];simpl;
        try discriminate;intro hyp;apply not_true_iff_false in hyp;
        (rewrite inclb_correct in hyp)
        || (rewrite eqX_correct in hyp)
        || clear hyp.
      + destruct_eqX v (@nil V);[exfalso;apply hyp,incl_nil|].
        destruct_eqX (v − u) (@nil V);
          [exfalso;apply hyp;intros a h1;case_in a u;
           [tauto|cut (a ∈ v − u);
                  [rewrite E;simpl;tauto|apply difference_spec;tauto]]|].
        destruct_eqX u (@nil V).
        * replace (v − []) with v by
              (clear;induction v;simpl;[|rewrite <- IHv];reflexivity).
          rewrite <- impl_Join.
          rewrite <- @eo_curry.
          apply eo_impl;[|reflexivity].
          rewrite @eo_and_comm. 
          symmetry;apply eo_inf_o_and.
          unfold_join;apply top'_a.
        * repeat rewrite <- impl_Join.
          rewrite <- @eo_curry.
          apply eo_impl;[|reflexivity].
          rewrite eo_impl_Join,map_map.
          rewrite and_Join,map_map.
          split_order;unfold__lat.
          -- apply difference_spec in ha as (ha1&ha2).
             etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;
                             split;[reflexivity|assumption]].
             unfold__lat;[|reflexivity].
             apply eo_heyting.
             assert (h : a ⌣ a0) by (intros <-;tauto).
             apply eq_obs_inf_obs.
             auto with equiv_obs.
          -- case_in a u.
             ++ etransitivity;[|apply eo_inf_bot].
                etransitivity;[|apply eq_obs_inf_obs,eo_contradict].
                apply obs_meet.
                ** apply eo_inf_and_right;reflexivity.
                ** apply eo_inf_and_left,eo_inf_in_Meet,in_map_iff.
                   exists a;tauto.
             ++ apply eo_inf_and_right,eo_inf_in_Join,in_map_iff.
                exists a;rewrite difference_spec;tauto.
      + destruct_eqX u (@nil V).
        * simpl;clear u E.
          split_order.
          -- unfold_join.
             apply eo_heyting,eo_inf_and_left,eo_inf_in_Join,in_map_iff.
             exists a ;tauto.
          -- case_prop (exists a, a ∈ v /\ a=a);
               [destruct hyp as (a&ha&_)
               |destruct v as [|a v];
                [clear hyp|exfalso;apply hyp;exists a;simpl;tauto]].
             ++ rewrite (eo_Ω_top' a__o a).
                rewrite @eo_impl_distr_left.
                apply eo_inf_and_right.
                rewrite <- (eo_Ω_neg v) at 1.
                rewrite <- @eo_curry.
                rewrite <- @eo_impl_distr_left.
                transitivity (⋁ (map o_obs (a::v))).
                ** etransitivity;[|apply eq_obs_inf_obs,eo_Ω_neg].
                   apply o_impl_inf;[apply o_impl_inf|];try reflexivity.
                ** unfold_join.
                   destruct ha0 as [->|ha0];
                     apply eo_inf_in_Join,in_map_iff;exists a0;tauto.
             ++ rewrite neg_top'_is_bot;reflexivity.
        * rewrite <- impl_Join.
          rewrite <- (eo_Ω_neg v).
          rewrite <- @eo_curry.
          rewrite <- @eo_impl_distr_left.
          rewrite <- @Join_app.
          rewrite <- map_app.
          symmetry;apply eo_Ω_neg.
      + pose proof hyp as e;apply eqX_false in e as ->.
        destruct_eqX v (@nil V);[rewrite interect_nil in hyp;tauto|].
        rewrite eo_impl_Join,map_map.
        split_order;unfold__lat.
        * rewrite eo_Meet_impl,map_map.
          unfold__lat.
          rewrite <- eo_curry.
          destruct_eqX a a0;[symmetry in E;subst|].
          -- rewrite eo_and_idem.
             apply eo_inf_in_Meet,in_map_iff;exists a.
             rewrite intersect_spec;tauto.
          -- etransitivity;[apply eo_inf_top|].
             apply eo_heyting.
             rewrite eo_and_comm,eo_and_top.
             rewrite <-eo_eq_bot_iff_inf_bot.
             apply eo_ax,jright,jleft,obs_incoh,N0.
        * apply intersect_spec in ha as (h1&h2).
          etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a;split;
                         [reflexivity|assumption]|].
          rewrite eo_Meet_impl,map_map.
          etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a;split;
                         [reflexivity|assumption]|].
          rewrite <- eo_curry,eo_and_idem;reflexivity.
      + destruct_eqX (u−v) (@nil V).
        * exfalso;apply hyp;intro a.
          assert (~ a ∈ u − v) as f by (now rewrite E;simpl).
          rewrite difference_spec in f;case_in a v;tauto.
        * clear N.
          rewrite eo_impl_Join,map_map.
          split_order;unfold__lat.
          -- case_in a v.
             ** etransitivity;[apply eo_inf_top|].
                apply eo_heyting;rewrite eo_and_comm,eo_and_top.
                apply eo_inf_in_Join,in_map_iff;exists a;tauto.
             ** etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a|].
                --- split;[reflexivity|apply difference_spec;tauto].
                --- apply o_impl_inf,eo_inf_bot;reflexivity.
          -- apply difference_spec in ha as (h1&h2).
             etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a|].
             ** split;[reflexivity|assumption].
             ** rewrite <- eo_heyting,eo_and_comm,eo_impl_premise.
                rewrite and_Join,map_map;unfold__lat.
                destruct_eqX a a0;[tauto|].
                rewrite <-eo_eq_bot_iff_inf_bot.
                apply eo_ax,jright,jleft,obs_incoh,N.
      + symmetry;apply eo_top_impl. 
      + symmetry;apply eo_top_impl. 
  Qed.
  
  Lemma τ_to_Obs__Ω s : axΩ ⊢ s ≡ τ (to_Obs__Ω s).
  Proof.
    induction s;try reflexivity.
    - simpl;symmetry;apply eo_or_bot.
    - rewrite IHs1,IHs2 at 1.
      rewrite <- τ_join__Ω;reflexivity.
    - rewrite IHs1,IHs2 at 1.
      rewrite <- τ_meet__Ω;reflexivity.
    - rewrite IHs1,IHs2 at 1.
      rewrite <- τ_impl__Ω;reflexivity.
  Qed.

  (** * Main results *)
  Theorem completeness_anticlique s t :
    axΩ ⊢ s ≦ t <-> s ≲ t.
  Proof.
    split.
    - apply inf_axΩ_sound. 
    - pose proof (τ_to_Obs__Ω s) as e;rewrite e at 2.
      apply eq_axΩ_sound in e;rewrite e at 1;clear e.
      pose proof (τ_to_Obs__Ω t) as e;rewrite e at 2.
      apply eq_axΩ_sound in e;rewrite e at 1;clear e.
      intro h.
      apply τ_proper_inf__Ω.
      intros a;pose proof (ζ_ξ a) as <-. 
      repeat rewrite <- sound_τ_sat__Ω;apply h.
  Qed.
 
  Corollary completeness_anticlique_eq s t :
    axΩ ⊢ s ≡ t <-> s ≃ t.
  Proof.
    rewrite (@inf_obs_partialorder Ω _ s t).
    unfold relation_conjunction,predicate_intersection,Basics.flip;simpl.
    repeat rewrite completeness_anticlique.
    symmetry;apply ssmaller_PartialOrder.
  Qed.

    Corollary ξ_to_Obs__Ω x s : x ⊨ (to_Obs__Ω s) <-> ξ x ⊨ s.
  Proof.
    pose proof (τ_to_Obs__Ω s) as e.
    apply completeness_anticlique_eq in e.
    rewrite e at 2.
    rewrite sound_τ_sat__Ω.
    rewrite ζ_ξ.
    reflexivity.
  Qed.
  
  Corollary sem_bij_to_Obs__Ω s t : to_Obs__Ω s ≲ to_Obs__Ω t <-> s ≲ t.
  Proof.
    unfold ssmaller.
    split;intros hyp.
    - intros α;rewrite <-(ξ_ζ α).
      setoid_rewrite <-ξ_to_Obs__Ω.
      apply hyp.
    - intros a.
      repeat  rewrite ξ_to_Obs__Ω.
      apply hyp.
  Qed.

  Instance dec_sat α (s : observation) : DecidableProp (α ⊨ s).
  Proof.
    pose proof (τ_to_Obs__Ω s) as e.
    apply eq_axΩ_sound in e.
    cut (DecidableProp (ζ α ⊨ (to_Obs__Ω s))).
    - intros h;apply (DecidableProp_equiv_prop h).
      rewrite <- sound_τ_sat__Ω,<-e;reflexivity.
    - generalize (to_Obs__Ω s) as o;clear e s;intros [[u|u]|];simpl;
        destruct (ζ α) as [a|];unfold satisfies,sat__Ω;
        (now left)||(now right)||typeclasses eauto.
  Qed.

  Instance anticlique_dec_inf (s t : observation) :
    DecidableProp (s ≲ t).
  Proof.
    apply (@DecidableProp_equiv_prop (to_Obs__Ω s ≲ to_Obs__Ω t)).
    - typeclasses eauto.
    - apply sem_bij_to_Obs__Ω.
  Qed.

  Lemma anticlique_inf_or_cntrex (s t : observation) :
    {s ≲ t} + {exists β, β ⊨ s /\ ~ β ⊨ t}.
  Proof.
    case_eq (to_Obs__Ω s);intros [u|u] e1||intros e1;case_eq (to_Obs__Ω t);
      intros [v|v] e2||intros e2.
    + case_prop (exists a, a ∈ v /\ ~ a ∈ u).
      * right;destruct hyp as (a&h1&h2);exists (ξ (Some a)).
        repeat rewrite <-ξ_to_Obs__Ω.
        rewrite e1,e2;unfold satisfies,sat__Ω.
        tauto.
      * left;apply sem_bij_to_Obs__Ω.
        rewrite e1,e2;apply complete_inf__Ω;simpl.
        apply inclb_correct;intros a ha.
        case_in a u;[tauto|].
        exfalso;apply hyp;exists a;tauto.
    + right.
      destruct (infiniteV (u++v)) as [a ha].
      exists (ξ (Some a)).
      repeat rewrite <-ξ_to_Obs__Ω.
      rewrite e1,e2;unfold satisfies,sat__Ω.
      rewrite in_app_iff in ha;tauto.
    + left;apply sem_bij_to_Obs__Ω.
      rewrite e1,e2;apply complete_inf__Ω;simpl.
      reflexivity.
    + case_prop (exists a, a∈ u /\ a ∈ v).
      * right.
        destruct hyp as (a&h1&h2);exists  (ξ (Some a)).
        repeat rewrite <-ξ_to_Obs__Ω.
        rewrite e1,e2;unfold satisfies,sat__Ω.
        tauto.
      * left;apply sem_bij_to_Obs__Ω.
        rewrite e1,e2;apply complete_inf__Ω;simpl.
        apply eqX_correct,incl_l_nil.
        intros a ha;apply hyp;exists a;apply intersect_spec,ha.
    + case_prop (exists a, a∈ u /\ ~ a ∈ v).
      * right.
        destruct hyp as (a&h1&h2);exists (ξ (Some a)).
        repeat rewrite <-ξ_to_Obs__Ω.
        rewrite e1,e2;unfold satisfies,sat__Ω.
        tauto.
      * left;apply sem_bij_to_Obs__Ω.
        rewrite e1,e2;apply complete_inf__Ω;simpl.
        apply inclb_correct;intros a ha.
        case_in a v;[|exfalso;apply hyp;exists a];tauto.
    + left;apply sem_bij_to_Obs__Ω.
      rewrite e1,e2;apply complete_inf__Ω;simpl.
      reflexivity.
    + right.
      exists (ξ None).
      repeat rewrite <-ξ_to_Obs__Ω;rewrite e1,e2;unfold satisfies,sat__Ω.
      tauto.
    + right.
      exists (ξ None).
      repeat rewrite <-ξ_to_Obs__Ω;rewrite e1,e2;unfold satisfies,sat__Ω.
      tauto.
    + left;apply sem_bij_to_Obs__Ω.
      rewrite e1,e2;apply complete_inf__Ω;simpl.
      reflexivity.
  Qed. 

  Proposition anticlique_choose_clique : choose_clique Ω.
  Proof.
    intros α s t.
    case_eq (ζ α).
    - intros a e.
      case_prop (α ⊨ s /\ ~ α ⊨ t).
      + right;exists α;split;[reflexivity|tauto].
      + left;intros β h.
        cut (β ≃ α).
        * intros -> h';case_prop (α ⊨ t);tauto.
        * intros b;split;[|apply h].
          intro h';apply mem_is_sgl in h'.
          rewrite h' in h.
          repeat rewrite mem_is_sgl;symmetry.
          revert h;pose proof (ξ_ζ α) as <-;rewrite e;simpl.
          intros h;apply mem_is_sgl,h,sgl_spec;reflexivity.
    - destruct (anticlique_inf_or_cntrex s t) as [h|h];intros e.
      + left;intros ? _;apply h.
      + right;destruct h as (β&h);exists β;split.
        pose proof (ξ_ζ α) as <-;rewrite e.
        * apply empt_max.
        * apply h.
  Qed.

End s.
