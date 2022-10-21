Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Import equiv_obs sem_obs laws.



Section s.
  Context { Idx : Set } { decIdx : decidable_set Idx }.
  Context { 𝖦 : Idx -> Graph } { dec𝖦 : forall i, DecidableGraph (𝖦 i) }.
  Context { choose_clique_𝖦 : forall i, choose_clique (𝖦 i)}.
  Notation V := (fun i => @vertex (𝖦 i)).
  
  Inductive 𝒱 : Set :=
  | node (i : Idx) (a : V i).

  Arguments node i a : clear implicits.
  Notation "  a @' i " := (node i a) (at level 5).

  Definition eq𝒱 (u v : 𝒱) : bool.
    destruct u,v as [j b].
    destruct_eqX i j.
    - exact (a =?= b).
    - exact false.
  Defined.
  Remark eq𝒱_proj1 i j a b : a@'i = b@'j -> i = j.
  Proof. intro h;inversion h as [h1];reflexivity. Qed.
  Remark eq𝒱_proj2 i a b : a@'i = b@'i -> a = b.
  Proof.
    intro h;inversion h as [h'].
    apply eq_sigT_iff_eq_dep in h'.
    apply eq_dep_eq in h';tauto.
  Qed.
         
  
  Inductive coh𝒢 : relation 𝒱 :=
  | coh_i i a b : a ⁐ b -> coh𝒢 a@'i b@'i
  | coh_ij i j a b : i <> j -> coh𝒢 a@'i b@'j.
  Hint Constructors coh𝒢 : core.
  
  Lemma coh𝒢_refl : Reflexive coh𝒢.
  Proof. intros [];apply coh_i;reflexivity. Qed.
  Lemma coh𝒢_sym : Symmetric coh𝒢.
  Proof.
    intros x y [i a b h|i j a b h].
    - now symmetry in h;auto.
    - apply coh_ij;intros ->;tauto.
  Qed.
  
  Instance 𝒢 : Graph := 
    {
    vertex := 𝒱;
    coh := coh𝒢;
    coh_refl := coh𝒢_refl;
    coh_sym := coh𝒢_sym
    }.

  Notation " a @ i " := (a @' i : @vertex 𝒢) (at level 20).
  
  Instance dec𝒢 : DecidableGraph 𝒢.
  Proof.
    split.
    - exists eq𝒱.
      intros [] [j b];simpl.
      case_eq (X_dec i j).
      + intros <- _.
        unfold eq_rect.
        destruct_eqX a b.
        * apply ReflectT;reflexivity.
        * apply ReflectF;intros E.
          apply eq𝒱_proj2 in E;tauto.
      + intros N _.
        apply ReflectF;intros E;inversion E;tauto.
    - intros [] [j b].
      destruct_eqX i j.
      + simpl;subst.
        case_prop (a ⁐ b);[left|right];auto.
        intro h;inversion h as [j' a' b' h1 h2 h3|].
        * subst.
          apply eq_sigT_iff_eq_dep in H.
          apply eq_dep_eq in H;subst.
          apply eq_sigT_iff_eq_dep in h3.
          apply eq_dep_eq in h3;subst.
          tauto.
        * tauto.
      + unfold coh;simpl;left;auto.
  Qed.

  Lemma incoh_iff_same_component_and_incoh u v :
    u ⌣ v <-> exists i a b, u = a@i /\ v = b@i /\ a ⌣ b.
  Proof.
    split.
    - intros f;destruct u as [i a],v as [j b].
      destruct_eqX j i;[subst|exfalso].
      + exists i, a, b;split;[|split];reflexivity||intros h;apply f,coh_i,h.
      + apply f;symmetry;apply coh_ij,N.
    - intros (i&a&b&->&->&h) f; inversion f.
      + apply eq_sigT_iff_eq_dep,eq_dep_eq in H1,H2;subst.
        apply h,H0.
      + apply H0;reflexivity.
  Qed.

  Lemma dec_in_proj i α v : DecidableProp (exists a, v = a@i /\ a ⊨ α).
  Proof.
    destruct v as [j a].
    destruct_eqX i j.
    - subst.
      case_prop (a ⊨ α).
      + left;simpl;firstorder.
      + right;intros (b&h1&h2).
        apply eq𝒱_proj2 in h1 as ->.
        tauto.
    - right;intros (b&h1&h2).
      apply eq𝒱_proj1 in h1 as ->.
      tauto.
  Qed.
  Lemma dec_compat_proj i α v : DecidableProp (exists a, v = a@i /\ a ⋊ α).
  Proof.
    destruct v as [j a].
    destruct_eqX i j.
    - subst.
      case_prop (a ⋊ α).
     + left;simpl;firstorder.
      + right;intros (b&h1&h2).
        apply eq𝒱_proj2 in h1 as ->.
        tauto.
    - right;intros (b&h1&h2).
      apply eq𝒱_proj1 in h1 as ->.
      tauto.
  Qed.

  Definition incompat_inject (i : Idx) (α : @clique (𝖦 i)) (a : 𝒱) 
    : option 𝒱.
    destruct a as [j a].
    destruct_eqX j i.
    - subst;destruct (incompat α a) as [b|].
      + exact (Some (b@i)).
      + exact None.
    - exact None.
  Defined.
        
    
  
  Definition inject i (α : @clique (𝖦 i)) : @clique 𝒢.
  Proof.
    exists (fun v => @test _ (dec_in_proj α v))
      (incompat_inject α).
    - intros u v.
      repeat rewrite Is_true_test.
      intros (a&->&ha)(b&->&hb).
      apply coh_i,(members_are_coh α);assumption.
    - intros [j a].
      unfold incompat_inject.
      destruct_eqX j i.
      + subst;simpl.
        case_eq (incompat α a);simpl.
        * intros b hb x e.
          inversion e;subst;clear e.
          rewrite Is_true_test.
          apply incompat_Some in hb as (h1&h2).
          split.
          -- exists b;split;[reflexivity|apply h1].
          -- apply incoh_iff_same_component_and_incoh.
             exists i, a, b;tauto.
        * discriminate.
      + discriminate.
    - intros [j a].
      unfold incompat_inject.
      destruct_eqX j i.
      + subst;simpl.
        case_eq (incompat α a);simpl.
        * discriminate.
        * intros h1 c _.
          rewrite Is_true_test.
          intros (b&->&hb).
          apply coh_i,(incompat_None _ h1),hb.
      + intros x _.
        rewrite Is_true_test.
        intros (b&->&hb).
        apply coh_ij,N.
  Defined.

  Remark inject_i_member (i : Idx) (v : @vertex 𝒢) (α : @clique (𝖦 i)) :
    v ⊨ (@inject i α) <-> (exists a : V i, v = a@i /\ a ⊨ α).
  Proof. simpl;apply Is_true_test. Qed.
  Remark inject_i_incompat i v α :
    v ⋊ inject α <-> (exists a, v = a@i /\ a ⋊ α).
  Proof.
    destruct v as [j a];simpl.
    destruct_eqX j i.
    - subst;simpl.
      case_eq (incompat α a);simpl.
      + intros b hb.
        split.
        * intros _;exists a;split;[|exists b];tauto.
        * intros _;exists (b@i);reflexivity.
      + intros h;split.
        * intros (?&f);discriminate.
        * intros (b&e&(c&e')).
          apply eq𝒱_proj2 in e;subst.
          rewrite e' in h;discriminate.
    - split.
      + intros (?&f);discriminate.
      + intros (b&e&(c&e')).
        apply eq𝒱_proj1 in e;subst;tauto.
  Qed.

  Opaque inject.

  
  Definition incompat_project (i : Idx) (α : clique) (a : V i) 
    : option (V i).
    case_eq (incompat α (a@i)).
    - intros [j b] e.
      destruct_eqX j i.
      + subst;exact (Some b).
      + exact None.
    - intros e;exact None.
  Defined.
  Definition project i (α : clique) : @clique (𝖦 i).
  Proof.
    exists (fun a => member α (a@i)) (incompat_project α).
    - intros a b h1 h2.
      pose proof (members_are_coh α _ _ h1 h2) as e.
      inversion e.
      + apply eq_sigT_iff_eq_dep,eq_dep_eq in H1,H2;subst.
        assumption.
      + tauto.
    - intros a b;simpl.
      unfold incompat_project;simpl.
      case_eq (incompat α (a@i)).
      + intros [j c] e.
        destruct_eqX j i.
        * subst;simpl.
          unfold eq_rec_r;simpl.
          intros e';inversion e';subst;clear e'.
          apply incompat_Some in e as (h1&h2);split;[assumption|].
          apply incoh_iff_same_component_and_incoh in h2 as
              (k&a'&b'&e1&e2&h).
          pose proof e1 as e'1;pose proof e2 as e'2.
          apply eq𝒱_proj1 in e1,e2;subst.
          apply eq𝒱_proj2 in e'1,e'2;subst.
          assumption.
        * discriminate.
      + discriminate.
    - intros a b;simpl.
      unfold incompat_project;simpl.
      case_eq (incompat α (a@i)).
      + intros [j c] e.
        destruct_eqX j i.
        * subst;simpl.
          unfold eq_rec_r;simpl.
          discriminate.
        * exfalso.
          apply incompat_Some in e as (_&f).
          apply incoh_iff_same_component_and_incoh in f
            as (k&?&?&f1&f2&_).
          apply eq𝒱_proj1 in f1,f2;subst;tauto.
      + intros h1 _ h2.
        case_prop (a ⁐ b);[tauto|].
        exfalso.
        cut (a@i ⁐ b@i).
        * apply incoh_iff_same_component_and_incoh.
          exists i,a,b;tauto.
        * apply incompat_None;assumption.
  Defined.

  Arguments project i α : clear implicits.

  Notation " α ⇂ i " := (project i α) (at level 5).

  Lemma project_spec i a α : a ⊨ (α ⇂ i) <-> (a @ i) ⊨ α.
  Proof. reflexivity. Qed.
                               

  Lemma project_inject i α : (inject α) ⇂ i ≃ α.
  Proof.
    intro a;simpl;rewrite project_spec,inject_i_member.
    split.
    - intros (?&e&h);apply eq𝒱_proj2 in e as <-.
      assumption.
    - intros h;exists a;tauto.
  Qed.
  
  Lemma join_project i α β :
    α ⇂ i ≲ β ->
    exists γ : clique, γ ⇂ i ≃ β /\ forall j, j <> i -> γ ⇂ j ≃ α ⇂ j.
  Proof.
    intro h.
    cut (exists z : clique, joins α (inject β) z).
    - intros (γ&hγ).
      exists γ;split.
      + intros a;simpl.
        rewrite (hγ (a @ i)).
        rewrite inject_i_member.
        split.
        * intros [ha|(b&e&hb)].
          -- apply h,ha.
          -- apply eq𝒱_proj2 in e as <-;assumption.
        * intros ha;right;exists a;tauto.
      + intros j n a;simpl.
        rewrite (hγ (a@j)),inject_i_member.
        split;[intros [?|(b&f&_)];[|apply eq𝒱_proj1 in f]|];tauto.
    - apply not_incompatible_is_joins.
      intros (u&v&ha&hv&huv).
      apply inject_i_member in hv as (b&->&hb).
      apply incoh_iff_same_component_and_incoh in huv
        as (j&a&b'&->&e&hab).
      pose proof e as e';apply eq𝒱_proj1 in e;symmetry in e;subst;
        apply eq𝒱_proj2 in e';symmetry in e';subst.
      apply hab,(members_are_coh β),hb.
      apply h,ha.
  Qed.
  Lemma join_project' i α β :
    α ⇂ i ≲ β -> exists γ : clique, γ ⇂ i ≃ β /\ α ≲ γ.
  Proof.
   intro h.
    destruct (join_project h) as (γ&h1&h2).
    exists γ;split;[assumption|].
    intros [j a].
    destruct_eqX j i.
    - subst;intro hyp;apply (h1 a),h,hyp.
    - rewrite (h2 _ N a);simpl;tauto.
  Qed.
  
  Notation 𝖳 := (fun i => @observation (𝖦 i)).

  Definition 𝒯 := @observation 𝒢.
  
  Fixpoint obs𝖦_to_𝒯 i (s : 𝖳 i) : 𝒯 :=
    match s with
    | ⦑a⦒ => ⦑a@i⦒
    | ⊤o => ⊤o
    | ⊥o => ⊥o
    | s1 ⟇ s2 => obs𝖦_to_𝒯 s1 ⟇ obs𝖦_to_𝒯 s2
    | s1 ⟑ s2 => obs𝖦_to_𝒯 s1 ⟑ obs𝖦_to_𝒯 s2
    | s1 → s2 => obs𝖦_to_𝒯 s1 → obs𝖦_to_𝒯 s2
    end.
  Arguments obs𝖦_to_𝒯 i s : clear implicits.

  Notation " s  .{ i }" := (obs𝖦_to_𝒯 i s) (at level 5).

  Lemma obs𝖦_to_𝒯_sat i s α :
    α ⊨ s.{i} <-> α ⇂ i ⊨ s.
  Proof.
    revert α;induction s;simpl;intro α;rsimpl;
      try tauto
      || (now intros α;rewrite IHs1,IHs2).
    - rewrite IHs1,IHs2;reflexivity.
    - rewrite IHs1,IHs2;reflexivity.
    - split.
      + intros h β h1 h2.
        destruct (join_project' h2) as (γ&hγ1&hγ2).
        rewrite <- hγ1 in *;clear β hγ1.
        apply IHs2,h,hγ2.
        apply IHs1,h1.
      + intros h β hβ1 hβ2.
        apply IHs2,h.
        * apply IHs1,hβ1.
        * intro a;simpl;apply hβ2.
  Qed.
  
  Lemma choose_clique_aux I (c d : forall i : Idx, 𝖳 i) α :
    (exists i, i ∈ I /\ forall β, α ≲ β -> β ⊨ (d i).{i} -> β ⊨ (c i).{i})
    \/ (exists β, α ≲ β /\ forall i, i ∈ I -> β ⊨ (d i).{i} /\ ~ β ⊨ (c i).{i}) .
  Proof.
    cut ((exists i, i ∈ I /\ forall β, α ≲ β -> β ⊨ (d i).{i} -> β ⊨ (c i).{i})
         \/(exists β, (forall i, ~ i ∈ I -> β⇂i ≃ α⇂i)
                /\ forall i, i ∈ I -> α⇂i ≲ β⇂i /\
                               β ⊨ (d i).{i} /\ ~ β ⊨ (c i).{i})) .
    - intros [h|(β&h1&h2)];[tauto|].
      right;exists β;split. 
      + intros [i a].
        case_in i I.
        * apply h2,I0.
        * apply h1,I0.
      + intros i hi;apply h2,hi.
    - induction I as [|i I].
      + right;exists α;split;simpl;[reflexivity|tauto].
      + destruct IHI as [(j&hj&h)|(β&hα&hβ)].
        * left;exists j;split;[now right|apply h].
        * case_in i I;[|destruct (@choose_clique_𝖦 i (α⇂i) (d i) (c i))
                         as [h'|(γ&hγ&hd&hc)]].
          -- right;exists β;split;[intros j hi;apply hα
                             |intros j [<-|hj];apply hβ];
             simpl in *; try tauto.
          -- left;exists i;split;[now left|].
             intros γ hγ.
             repeat rewrite obs𝖦_to_𝒯_sat.
             apply h';intro a;simpl;apply hγ.
          -- right.
             pose proof hγ as hαγ.
             rewrite <- hα in hγ by assumption.
             apply join_project in hγ as (δ&hγ&hδ).
             exists δ;split;intros j hj;[ |destruct hj as [<-|hj]].
             ++ rewrite hδ by (intros ->;simpl in hj;tauto).
                apply hα;simpl in hj;tauto.
             ++ repeat rewrite obs𝖦_to_𝒯_sat,hγ;tauto.
             ++ pose proof (hβ _ hj) as hyp1.
                assert (hyp2 : j <> i) by (intros ->;tauto).
                apply hδ in hyp2.
                split;[rewrite hyp2;tauto|].
                destruct hyp1 as (_&hyp1).
                clear hα hβ hδ hd hc hj hγ hαγ γ α I I0.
                repeat rewrite obs𝖦_to_𝒯_sat in *.
                rewrite hyp2;assumption.
  Qed.

  Definition termVect := forall i : Idx, 𝖳 i.
  Definition NF := list termVect.
  Definition mapNF : list Idx -> termVect -> list 𝒯 :=
    fun l x => map (fun i => (x i).{i}) l.

  Definition conj_interp : list Idx -> list termVect -> 𝒯 :=
    fun l v => ⋀ (map (fun x => ⋁ (mapNF l x)) v).
  Definition disj_interp : list Idx -> list termVect -> 𝒯 :=
    fun l v => ⋁ (map (fun x => ⋀ (mapNF l x)) v).
  
  (* Global Instance conj_interp_proper : *)
  (*   Proper (@equivalent Idx ==> @equivalent termVect ==> equiv_Obs ha_ax) *)
  (*          conj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold conj_interp. *)
  (*   etransitivity;[eapply Meet_equiv;rewrite E2;reflexivity|]. *)
  (*   apply Meet_map_equiv_pointwise;intros. *)
  (*   unfold mapNF. *)
  (*   apply Join_equiv;rewrite E1;reflexivity. *)
  (* Qed. *)
  (* Global Instance disj_interp_proper : *)
  (*   Proper (@equivalent Idx ==> @equivalent termVect ==> equiv_Obs HA) *)
  (*          disj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold disj_interp. *)
  (*   assert (e: HA⇚HA) by reflexivity. *)
  (*   etransitivity;[eapply Join_equiv;rewrite E2;reflexivity|]. *)
  (*   apply Join_map_equiv_pointwise;intros. *)
  (*   unfold mapNF. *)
  (*   apply Meet_equiv;rewrite E1;reflexivity. *)
  (* Qed. *)
  (* Global Instance conj_interp_proper_inf : *)
  (*   Proper (@incl Idx ==> Basics.flip (@incl termVect) ==> inf_obs HA) *)
  (*          conj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold conj_interp. *)
  (*   assert (e: HA⇚HA) by reflexivity. *)
  (*   unfold_meet. *)
  (*   apply E2 in ha. *)
  (*   etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a;split; *)
  (*                  [reflexivity|assumption]|]. *)
  (*   unfold_join. *)
  (*   apply E1 in ha0. *)
  (*   apply eo_inf_in_Join,in_map_iff;exists a0;tauto. *)
  (* Qed. *)
  (* Global Instance disj_interp_proper_inf : *)
  (*   Proper (Basics.flip(@incl Idx) ==> @incl termVect ==> ax_inf HA) *)
  (*          disj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold disj_interp. *)
  (*   assert (e: HA⇚HA) by reflexivity. *)
  (*   unfold_join. *)
  (*   apply E2 in ha. *)
  (*   etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;split; *)
  (*                   [reflexivity|assumption]]. *)
  (*   unfold_meet. *)
  (*   apply E1 in ha0. *)
  (*   apply eo_inf_in_Meet,in_map_iff;exists a0;tauto. *)
  (* Qed. *)
  
  Context { 𝖠 : forall i : Idx, relation (@observation (𝖦 i)) }.
  Arguments 𝖠 i : clear implicits.
  
  Hypothesis 𝖠_complete :
    forall i, forall s t : 𝖳 i, 𝖠 i ⊢ s ≡ t <-> s ≃ t.
  Corollary 𝖠_complete_inf :
    forall i, forall s t : 𝖳 i, 𝖠 i ⊢ s ≦ t <-> s ≲ t.
  Proof.
    intros i s t;unfold inf_obs;rewrite 𝖠_complete.
    split;intros e α;simpl.
    - rewrite <- (e α);simpl;rsimpl;tauto.
    - split;[intros [h|h];[apply e|]|];rsimpl;tauto.
  Qed.

  Reserved Notation " x =𝒜 y " (at level 80).
  Inductive prod_ax : relation 𝒯 :=
  | prod_idx i s t : 𝖠 i s t -> s.{i} =𝒜 t.{i}
  | prod_impl idx x y :
      (⋀ (mapNF idx x) → ⋁ (mapNF idx y))
      =𝒜  ⋁ (mapNF idx (fun i => x i → y i))
  where " x =𝒜 y " := (prod_ax x y).
  Notation 𝒜 := (ha_ax (+) (obs_ax (+) prod_ax)).

  Remark eo_prod_impl idx x y :
    𝒜 ⊢ (⋀ (mapNF idx x) → ⋁ (mapNF idx y))
      ≡ ⋁ (mapNF idx (fun i => x i → y i)).
  Proof. apply eo_ax,jright,jright,prod_impl. Qed.
  

  (* Instance 𝒜_Obs : Obs ⇚ 𝒜. *)
  (* Proof. intros s t h;apply eo_ax,prod_obs,h. Qed. *)
  (* Global Instance 𝒜_HA : HA ⇚ 𝒜. *)
  (* Proof. intros s t h;apply eo_ax,prod_obs,obs_ha,h. Qed. *)

  Instance obs𝖦_to_𝒯_proper i :
    Proper (equiv_Obs (𝖠 i) ==> equiv_Obs 𝒜) (obs𝖦_to_𝒯 i).
  Proof.
    intros s t e;remember (𝖠 i) as A. 
    induction e;subst;auto with equiv_obs.
    - etransitivity;[apply IHe1|apply IHe2];reflexivity.
    - simpl;rewrite IHe1,IHe2 by reflexivity;reflexivity.
    - simpl;rewrite IHe1,IHe2 by reflexivity;reflexivity.
    - simpl;rewrite IHe1,IHe2 by reflexivity;reflexivity.
    - apply eo_ax,jright,jright,prod_idx,H.
  Qed.
  
  Instance obs𝖦_to_𝒯_proper_inf i :
    Proper (inf_obs (𝖠 i) ==> inf_obs 𝒜) (obs𝖦_to_𝒯 i).
  Proof. intros s t e;apply obs𝖦_to_𝒯_proper in e;apply e. Qed.
    
  (* Definition disj_incl_NF : relation NF := *)
  (*   fun u v => *)
  (*     forall x, x ∈ u -> exists y, y ∈ v /\ forall i, x i ≲ y i. *)
  (* Definition conj_incl_NF : relation NF := *)
  (*   fun u v => *)
  (*     forall x, x ∈ v -> exists y, y ∈ u /\ forall i, y i ≲ x i. *)
   
  (* Global Instance conj_interp_proper_inf' : *)
  (*   Proper (@incl Idx ==> conj_incl_NF ==> ax_inf 𝒜) *)
  (*          conj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold conj_interp. *)
  (*   assert (e: HA⇚HA) by reflexivity. *)
  (*   unfold_meet. *)
  (*   apply E2 in ha as (y&hy1&hy2). *)
  (*   etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists y;split; *)
  (*                  [reflexivity|assumption]|]. *)
  (*   unfold_join. *)
  (*   apply E1 in ha. *)
  (*   etransitivity;[| apply eo_inf_in_Join,in_map_iff;exists a0;tauto]. *)
  (*   apply obs𝖦_to_𝒯_proper_inf. *)
  (*   apply 𝖠_complete_inf. *)
  (*   apply hy2. *)
  (* Qed. *)

  (* Global Instance disj_interp_proper_inf' : *)
  (*   Proper (Basics.flip (@incl Idx) ==> disj_incl_NF ==> ax_inf 𝒜) *)
  (*          disj_interp. *)
  (* Proof. *)
  (*   intros l m E1 u v E2;unfold disj_interp. *)
  (*   assert (e: HA⇚HA) by reflexivity. *)
  (*   unfold_join. *)
  (*   apply E2 in ha as (y&hy1&hy2). *)
  (*   etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists y;split; *)
  (*                  [reflexivity|assumption]]. *)
  (*   unfold_meet. *)
  (*   apply E1 in ha. *)
  (*   etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a0;tauto|]. *)
  (*   apply obs𝖦_to_𝒯_proper_inf. *)
  (*   apply 𝖠_complete_inf. *)
  (*   apply hy2. *)
  (* Qed. *)
 
  Lemma 𝒜_sound : subrelation 𝒜 sequiv.
  Proof.
    intros _ _ [s t h|_ _ [s t h|_ _ [s t i h|I d c]]].
    - apply ha_sound,h.
    - apply Obs_sound,jright,h.
    - apply eo_ax,𝖠_complete in h.
      intro a;rewrite obs𝖦_to_𝒯_sat,h,<-obs𝖦_to_𝒯_sat.
      reflexivity.
    - intros α;split.
      + intros h;simpl in h.
        destruct (choose_clique_aux I c d α)
          as [(i&hi&hα)|(β&hα&hβ)].
        * apply satisfies_Join.
          eexists;split;
            [apply in_map_iff;exists i;split;
             [reflexivity|apply hi]|].
          simpl;intros β h1 h2;apply hα;tauto.
        * exfalso.
          pose proof (h β) as f;revert f;clear h.
          intros h.
          cut (β ⊨ (⋀ (mapNF I d))).
          -- intro f;apply h in f;[|assumption].
             apply satisfies_Join in f as (x&hx&f).
             apply in_map_iff in hx as (i&<-&hi).
             apply (hβ _ hi),f.
          -- apply satisfies_Meet.
             intros x hx; apply in_map_iff in hx as (i&<-&hi).
             apply hβ,hi.
      + intros h;apply satisfies_Join in h as (o&ho&h).
        apply in_map_iff in ho as (i&<-&hi).
        rsimpl.
        intros β h1 h2.
        rewrite satisfies_Meet in h1.
        apply satisfies_Join;eexists ;split;
          [apply in_map_iff;exists i;split;[reflexivity|assumption]|].
        simpl in h;apply h,h2.
        apply h1,in_map_iff;exists i;tauto.
  Qed.

  Definition dnf_support (dnf : NF) I :=
    forall n i, n ∈ dnf -> ~ i ∈ I -> (n i) = ⊤o.
  Definition cnf_support (cnf : NF) I :=
    forall n i, n ∈ cnf -> ~ i ∈ I -> (n i) = ⊥o.

  Fixpoint dnf_to_cnf I (dnf : NF) :=
    match dnf with
    | [] => [fun _ => ⊥o]
    | n::d => (flat_map (fun nc =>
                         map (fun i j =>
                                if i =?= j
                                then (n j ⟇ nc j)
                                else (nc j))
                             I) (dnf_to_cnf I d))
    end.
  Fixpoint cnf_to_dnf I (cnf : NF) :=
    match cnf with
    | [] => [fun _ => ⊤o]
    | n::c => (flat_map (fun nd =>
                         map (fun i j =>
                                if i =?= j
                                then (n j ⟑ nd j)
                                else (nd j))
                             I) (cnf_to_dnf I c))
    end.
  Lemma cnf_to_dnf_support I c : dnf_support (cnf_to_dnf I c) I.
  Proof.
    induction c;simpl;intros x i.
    - intros [<-|F];[reflexivity|simpl in *;tauto].
    - intros h1 h2.
      apply in_flat_map in h1 as (y&h1&h3).
      apply in_map_iff in h3 as (j&<-&hj).
      destruct_eqX j i;[tauto|].
      apply IHc;tauto.
  Qed.
  Lemma dnf_to_cnf_support I d : cnf_support (dnf_to_cnf I d) I.
  Proof.
    induction d;simpl;intros x i.
    - intros [<-|F];[reflexivity|simpl in *;tauto].
    - intros h1 h2.
      apply in_flat_map in h1 as (y&h1&h3).
      apply in_map_iff in h3 as (j&<-&hj).
      destruct_eqX j i;[tauto|].
      apply IHd;tauto.
  Qed.
  Lemma cnf_to_dnf_equiv I c :
    𝒜 ⊢ disj_interp I (cnf_to_dnf I c) ≡ conj_interp I c.
  Proof.
    induction c as [|n c];unfold conj_interp,disj_interp;simpl.
    - rewrite eo_or_bot.
      apply eo_eq_top_iff_top_inf.
      unfold__lat;reflexivity.
    - rewrite <- IHc;unfold disj_interp;clear IHc.
      generalize (cnf_to_dnf I c) as d;clear c;intro d.
      setoid_rewrite and_Join.
      setoid_rewrite map_map;simpl.
      rewrite flat_map_concat_map.
      rewrite concat_map,map_map,<-flat_map_concat_map.
      rewrite @flat_map_Join.
      repeat rewrite map_map.
      apply Join_map_equiv_pointwise;intros nc _;simpl.
      rewrite map_map.
      rewrite eo_and_comm.
      rewrite and_Join.
      unfold mapNF.
      repeat rewrite map_map.
      apply Join_map_equiv_pointwise.
      intros i hi.
      rewrite eo_and_comm.
      split_order;unfold__lat.
      * etransitivity;[apply eo_inf_in_Meet,in_map_iff;
                       eexists;split;[reflexivity|apply hi]|].
        destruct_eqX i i;[simpl|tauto].
        apply eo_inf_and_left;reflexivity.
      * etransitivity;[apply eo_inf_in_Meet,in_map_iff;
                       eexists;split;[reflexivity|apply ha]|].
        destruct_eqX i a;[|reflexivity].
        apply eo_inf_and_right;reflexivity.
      * destruct_eqX i a;simpl.
        -- unfold__lat;[apply eo_inf_and_left;reflexivity|].
           apply eo_inf_and_right,eo_inf_in_Meet,in_map_iff.
           exists a;tauto.
        -- apply eo_inf_and_right,eo_inf_in_Meet,in_map_iff.
           exists a;split;auto.  
  Qed.
  
  
  Lemma dnf_to_cnf_equiv I (dnf : NF) :
    𝒜 ⊢ conj_interp I (dnf_to_cnf I dnf) ≡ disj_interp I dnf.
  Proof.
    symmetry;unfold conj_interp,disj_interp;
      induction dnf as [|n d];simpl.
    - simpl.
      rewrite eo_and_top.
      symmetry;apply eo_eq_bot_iff_inf_bot.
      unfold__lat;reflexivity.
    - rewrite IHd;clear IHd.
      generalize (dnf_to_cnf I d) as c;clear d;intro c.
      setoid_rewrite or_Meet.
      setoid_rewrite map_map;simpl.
      rewrite flat_map_concat_map.
      rewrite concat_map,map_map,<-flat_map_concat_map.
      rewrite @flat_map_Meet.
      repeat rewrite map_map.
      apply Meet_map_equiv_pointwise;intros nc _;simpl.
      rewrite map_map.
      rewrite eo_or_comm.
      rewrite or_Meet.
      unfold mapNF.
      repeat rewrite map_map.
      apply Meet_map_equiv_pointwise.
      intros i hi.
      rewrite eo_or_comm.
      split_order;unfold__lat.
      * etransitivity;[|apply eo_inf_in_Join,in_map_iff;
                        eexists;split;[reflexivity|apply hi]].
        destruct_eqX i i;[|tauto].
        apply eo_inf_or_left;reflexivity.
      * etransitivity;[|apply eo_inf_in_Join,in_map_iff;
                        eexists;split;[reflexivity|apply ha]].
        destruct_eqX i a;[|reflexivity].
        apply eo_inf_or_right;reflexivity.
      * destruct_eqX i a;simpl.
        -- unfold__lat;[apply eo_inf_or_left;reflexivity|].
           apply eo_inf_or_right,eo_inf_in_Join,in_map_iff.
           exists a;tauto.
        -- apply eo_inf_or_right,eo_inf_in_Join,in_map_iff.
           exists a;split;auto.  
  Qed.
  
  Instance cnf_support_proper_incl c :
    Proper (@incl Idx ==> Basics.impl) (cnf_support c).
  Proof.
    intros I J h1 h2 n i hn hi;apply h2;[apply hn|intro f;apply hi,h1,f].
  Qed.
  Instance dnf_support_proper_incl d :
    Proper (@incl Idx ==> Basics.impl) (dnf_support d).
  Proof.
    intros I J h1 h2 n i hn hi;apply h2;[apply hn|intro f;apply hi,h1,f].
  Qed.
  Instance cnf_support_proper c :
    Proper (@equivalent Idx ==> iff) (cnf_support c).
  Proof.
    intros I J h1;split;apply cnf_support_proper_incl;
      rewrite h1;reflexivity.
  Qed.
  Instance dnf_support_proper d :
    Proper (@equivalent Idx ==> iff) (dnf_support d).
  Proof.
    intros I J h1;split;apply dnf_support_proper_incl;
      rewrite h1;reflexivity.
  Qed.
  
  Lemma cnf_support_incl I J (cnf : NF) :
    cnf_support cnf I -> I ⊆ J ->
    𝒜 ⊢ conj_interp I cnf ≡ conj_interp J cnf.
  Proof.
    intros h1 h2;split_order;unfold__lat.
    - etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a;split;
                     [reflexivity|assumption]|].
      unfold__lat.
      apply eo_inf_in_Join,in_map_iff;exists a0;split;
        [reflexivity|apply h2,ha0].
    - etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists a;split;
                     [reflexivity|assumption]|].
      unfold__lat.
      case_in a0 I.
      + apply eo_inf_in_Join,in_map_iff;exists a0;split;
          [reflexivity|assumption].
      + rewrite (h1 a a0 ha I0);apply eo_inf_bot.
  Qed.
  
  Lemma dnf_support_incl I J (dnf : NF) :
     dnf_support dnf I -> I ⊆ J ->
      𝒜 ⊢ disj_interp I dnf ≡ disj_interp J dnf.
  Proof.
    intros h1 h2;split_order;unfold__lat.
    - etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;split;
                     [reflexivity|assumption]].
      unfold__lat.
      case_in a0 I.
      + apply eo_inf_in_Meet,in_map_iff;exists a0;split;
          [reflexivity|assumption].
      + rewrite (h1 a a0 ha I0);apply eo_inf_top.
    - etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists a;split;
                     [reflexivity|assumption]].
      unfold__lat.
      apply eo_inf_in_Meet,in_map_iff;exists a0;split;
        [reflexivity|apply h2,ha0].
  Qed.

  Definition atTop i (a : V i) : termVect.
    intros j;destruct_eqX j i.
    - subst;exact (o_obs a).
    - exact ⊤o.
  Defined.

  Fixpoint sup s :=
    match s with
    | ⊤o | ⊥o => []
    | ⦑_@'i⦒ => [i]
    | s⟇t | s⟑t | s → t => sup s ++ sup t
    end.
  
  Fixpoint normal_form s : list termVect:=
    match s with
    | ⊤o => [fun _ => ⊤o]
    | ⊥o => []
    | ⦑a@'i⦒ => [atTop a]
    | s ⟇ t => (normal_form s)++(normal_form t)
    | s ⟑ t =>
      cnf_to_dnf (sup s++sup t)
                 ((dnf_to_cnf (sup s++sup t) (normal_form s))
                    ++(dnf_to_cnf (sup s++sup t) (normal_form t)))
    | s → t =>
      cnf_to_dnf (sup s++sup t)
                 (map (fun p i => (snd p i→fst p i))
                      (pairs (dnf_to_cnf (sup s++sup t)
                                         (normal_form t))
                             (normal_form s)))
    end.

  Lemma normal_form_sup s : dnf_support (normal_form s) (sup s).
  Proof.
    induction s.
    - intros x i;simpl;intros [<-|F] _;simpl;tauto.
    - intros x i;simpl;tauto.
    - intros x i;simpl;destruct v as [j a];simpl;unfold atTop.
      intros [<-|F] h;simpl;try tauto.
      destruct_eqX i j;subst;simpl;tauto.
    - intros x i;simpl;simpl_In.
      intros [h|h] hyp.
      + apply IHs1;tauto.
      + apply IHs2;tauto.
    - simpl;apply cnf_to_dnf_support.
    - simpl;apply cnf_to_dnf_support.
  Qed.
        
  Lemma normal_form_eq s :
    𝒜 ⊢ s ≡ disj_interp (sup s) (normal_form s).
  Proof.
    induction s;simpl.
    - unfold disj_interp;simpl.
      rewrite eo_or_bot.
      reflexivity.
    - reflexivity. 
    - destruct v as [i a];unfold disj_interp;simpl.
      rewrite eo_or_bot.
      rewrite eo_and_top.
      unfold atTop;destruct_eqX i i;[|tauto];simpl.
      reflexivity.
    - rewrite IHs1,IHs2 at 1.
      rewrite (@dnf_support_incl (sup s1) (sup s1++sup s2))
        by (apply normal_form_sup||apply incl_appl;reflexivity).
      rewrite (@dnf_support_incl (sup s2) (sup s1++sup s2))
        by (apply normal_form_sup||apply incl_appr;reflexivity).
      unfold disj_interp;rewrite map_app.
      symmetry;apply Join_app.
    - rewrite IHs1,IHs2 at 1.
      rewrite (@dnf_support_incl (sup s1) (sup s1++sup s2))
        by (apply normal_form_sup||apply incl_appl;reflexivity).
      rewrite (@dnf_support_incl (sup s2) (sup s1++sup s2))
        by (apply normal_form_sup||apply incl_appr;reflexivity).
      rewrite <- (dnf_to_cnf_equiv).
      rewrite <- (dnf_to_cnf_equiv _ (normal_form s2)).
      rewrite cnf_to_dnf_equiv.
      unfold conj_interp.
      rewrite map_app;symmetry;apply Meet_app.
    - rewrite cnf_to_dnf_equiv.
      rewrite IHs1,IHs2 at 1.
      pose proof (@normal_form_sup s1) as hs1.
      pose proof (@normal_form_sup s2) as hs2.
      revert hs1 hs2.
      generalize (normal_form s1) as d1,(normal_form s2) as d2.
      generalize (sup s1) as I1,(sup s2) as I2.
      clear IHs1 IHs2 s1 s2;intros.
      rewrite (@dnf_support_incl I1 (I1++I2))
        by (apply hs1||apply incl_appl;reflexivity).
      rewrite (@dnf_support_incl I2 (I1++I2))
        by (apply hs2||apply incl_appr;reflexivity).
      rewrite <- (dnf_to_cnf_equiv _ d2).
      assert (dnf_support d1 (I1++I2)
              /\ cnf_support (dnf_to_cnf (I1++I2) d2) (I1++I2))
             as (h1&h2)
        by (split;[apply (@dnf_support_proper_incl d1 I1 (I1++I2));
                   [apply incl_appl|apply hs1];reflexivity
                  | apply dnf_to_cnf_support]).
      generalize dependent (dnf_to_cnf (I1++I2) d2).
      generalize dependent (I1++I2);clear hs1 hs2 d2.
      intros l h1 c h2.
      unfold disj_interp.
      rewrite @eo_impl_Join,map_map. 
      split_order.
      + unfold__lat.
        apply in_map_iff in ha as ((x&y)&<-&ha).
        apply pairs_spec in ha as (hx&hy).
        etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists y;split;
                       [reflexivity|assumption]|].
        unfold conj_interp.
        rewrite @eo_Meet_impl,map_map.
        etransitivity;[apply eo_inf_in_Meet,in_map_iff;exists x;split;
                       [reflexivity|assumption]|].
        rewrite eo_prod_impl.
        unfold_join;simpl.
        apply eo_inf_in_Join,in_map_iff;exists a;simpl;tauto.
      + unfold__lat.
        apply eo_heyting.
        unfold__lat.
        unfold conj_interp.
        etransitivity;[apply o_and_inf;
                       [apply eo_inf_in_Meet,in_map_iff;
                        eexists;split;[reflexivity|];
                        apply in_map_iff;
                        exists (a0,a);split;[reflexivity|];
                        apply pairs_spec;split;tauto
                       |reflexivity]|].
        simpl.
        rewrite @eo_and_comm,@and_Join.
        unfold_join.
        apply in_map_iff in ha1 as (i&<-&hi).
        etransitivity;[apply o_and_inf;
                       [apply eo_inf_in_Meet,in_map_iff;
                        exists i;split;[reflexivity|assumption]
                       |reflexivity]|].
        simpl;rewrite @eo_impl_premise.
        apply eo_inf_and_right,eo_inf_in_Join,in_map_iff.
        exists i;tauto.
  Qed.

  
  Theorem 𝒜_complete s t :
    𝒜 ⊢ s ≡ t <-> s ≃ t.
  Proof.
    split;[apply eo_sound,𝒜_sound|revert s t].
    cut (forall s t, s ≃ t -> 𝒜 ⊢ s ≦ t);
      [intros h s t h';split_order;apply h;rewrite h';reflexivity|].
    intros s t h.
    apply eo_inf_o_impl.
    pose proof (normal_form_eq (s→ t)) as E.
    rewrite E.
    apply eo_sound in E;[|apply 𝒜_sound].
    cut (empt ⊨ (s → t));[|intros β h1 h2;apply h,h1].
    intros X;apply E,satisfies_Join in X as (o&ho&he).
    apply in_map_iff in ho as (n&<-&hn).
    rewrite (satisfies_Meet empt (mapNF (sup (s→t)) n )) in he.
    setoid_rewrite in_map_iff in he.
    cut (forall i, i ∈ sup (s→t) -> empt ⊨ (n i).{i});
      [|intros;apply he;exists i;tauto].
    clear he;intro he.
    clear E h.
    etransitivity;[|apply eo_inf_in_Join,in_map_iff;exists n;split;
                    [reflexivity|assumption]].
    unfold__lat.
    apply eo_eq_top_iff_top_inf.
    apply he in ha;simpl in ha.
    apply obs𝖦_to_𝒯_sat in ha.
    replace ⊤o with (⊤o.{a}) by reflexivity.
    apply obs𝖦_to_𝒯_proper,𝖠_complete.
    intros α;simpl;split;[rsimpl;tauto|intros _].
    assert (empt⇂a≲α) as <- by (intro;unfold satisfies,satClique;simpl;
                               tauto).
    assumption.
  Qed.
    
  Instance product_sat_dec :
    forall α s, DecidableProp (α ⊨ s).
  Proof.
    assert (sat_dec_i : forall i α (s : 𝖳 i), DecidableProp (α ⊨ s))
      by (intro i;apply choose_clique_sat_dec,choose_clique_𝖦).
    intros α s.
    apply (@DecidableProp_equiv_prop
             (α ⊨ (disj_interp (sup s) (normal_form s)))).
    - apply (@DecidableProp_equiv_prop
               (exists n, n ∈ normal_form s
                     /\ forall i, i ∈ sup s -> α ⇂ i ⊨ (n i))).
      + typeclasses eauto.
      + unfold disj_interp,mapNF.
        rewrite satisfies_Join.
        setoid_rewrite in_map_iff.
        split.
        * intros (n&hn&hi).
          eexists ;split.
          -- exists n;split;[reflexivity|assumption].
          -- apply satisfies_Meet.
             intros x h;apply in_map_iff in h as [a [<- ha]].
             apply obs𝖦_to_𝒯_sat,hi,ha.
        * intros (x&(n&<-&hn)&hs).
          exists n;split;[assumption|].
          intros i hi;apply obs𝖦_to_𝒯_sat.
          eapply satisfies_Meet;[apply hs|].
          apply in_map_iff;exists i;tauto.
    - pose proof (normal_form_eq s) as e.
      apply 𝒜_complete in e as <-;reflexivity.
  Qed.

  Lemma auxiliary  i I α β γ :
     α ≲ β -> α ⇂ i ≲ γ ->
    exists δ : clique,
      (α ≲ δ) /\ (δ ⇂ i ≃ γ)
      /\ (forall j : Idx, i <> j ->j ∈ I -> δ ⇂ j ≃ β ⇂ j).
  Proof.
    intros h1 h2.
    apply join_project' in h2 as (γ'&e&h2).
    setoid_rewrite <- e;clear γ e.
    set (δ_mem :=
           fun v =>
             match v with
             | _@'k =>
               if k=?=i
               then member γ' v
               else
                 if test (k ∈ I)
                 then member β v
                 else member α v
             end).
    set (δ_incomp :=
           fun v =>
             match v with
             | _@'k =>
               if k=?=i
               then incompat γ' v
               else
                 if test (k ∈ I)
                 then incompat β v
                 else incompat α v
             end).
    assert ((forall a b : vertex,
                Is_true (δ_mem a) -> Is_true (δ_mem b) -> a ⁐ b)
            /\ (forall a b : vertex,
                  δ_incomp a = Some b -> Is_true (δ_mem b) /\ a ⌣ b)
            /\ (forall a b : vertex,
                  δ_incomp a = None -> Is_true (δ_mem b) -> a ⁐ b ))
      as (mac&iS&iN).
    - split;[|split].
      + intros [k a] [k' b];simpl;destruct_eqX k' k;subst.
        * destruct_eqX k i;[|case_in k I];subst.
          -- rewrite eqX_refl.
             apply (members_are_coh γ').
          -- apply test_spec in I0 as ->.
             apply (members_are_coh β).
          -- rewrite <- (@test_spec (k∈I)),not_true_iff_false in I0.
             rewrite I0.
             apply (members_are_coh α).
        * intros;apply coh_ij;intros ->;tauto.
      + intros [k a] b;simpl.
        destruct_eqX k i;[|case_in k I];subst.
        * rewrite eqX_refl;intro h.
          apply (incompat_Some _ γ') in h as (h3&h4).
          pose proof h4 as e.
          apply incoh_iff_same_component_and_incoh in e
            as (j&?&?&f1&f2&_);symmetry in f1.
          apply eq𝒱_proj1 in f1;subst.
          simpl;rewrite eqX_refl;tauto.
        * apply test_spec in I0;rewrite I0.
          intro h.
          apply (incompat_Some _ β) in h as (h3&h4).
          pose proof h4 as e.
          apply incoh_iff_same_component_and_incoh in e
            as (j&?&?&f1&f2&_);symmetry in f1.
          apply eq𝒱_proj1 in f1;subst.
          simpl;simpl_eqX;rewrite I0.
          tauto.
        * rewrite <- (@test_spec (k∈I)),not_true_iff_false in I0.
          rewrite I0.
          intro h.
          apply (incompat_Some _ α) in h as (h3&h4).
          pose proof h4 as e.
          apply incoh_iff_same_component_and_incoh in e
            as (j&?&?&f1&f2&_);symmetry in f1.
          apply eq𝒱_proj1 in f1;subst.
          simpl;simpl_eqX;rewrite I0.
          tauto.
      + intros [k a] [k' b];simpl;destruct_eqX k' k;subst.
        * destruct_eqX k i;[|case_in k I];subst.
          -- rewrite eqX_refl.
             apply (@incompat_None _ γ').
          -- apply test_spec in I0 as ->.
             apply (@incompat_None _ β).
          -- rewrite <- (@test_spec (k∈I)),not_true_iff_false in I0.
             rewrite I0.
             apply (@incompat_None _ α).
        * intros;apply coh_ij;intros ->;tauto.
    - exists (Build_clique mac iS iN);split;[|split].
      + intros [k a];simpl.
        destruct_eqX k i;[|case_in k I];subst;unfold satisfies,satClique;
          simpl.
        * rewrite eqX_refl.
          apply h2.
        * apply test_spec in I0 as ->.
          apply eqX_false in N as ->.
          apply h1.
        * rewrite <- (@test_spec (k∈I)),not_true_iff_false in I0.
          rewrite I0.
          apply eqX_false in N as ->.
          tauto.
      + intros a;simpl.
        unfold satisfies,satClique;simpl.
        rewrite eqX_refl;reflexivity.
      + intros j h3 h4 a;simpl.
        unfold satisfies,satClique; simpl;simpl_eqX.
        apply test_spec in h4 as ->.
        reflexivity.
  Qed.
      
  Lemma product_choose_clique : choose_clique 𝒢.
  Proof.
    intros α s t.
    set (dnf := normal_form s).
    set (cnf := dnf_to_cnf (sup t) (normal_form t)).
    set (I := sup s ++ sup t).
    cut ({forall β : clique, α ≲ β ->
                        β ⊨ (disj_interp I dnf) ->
                        β ⊨ (conj_interp I cnf)} +
         {exists β : clique, (α ≲ β) /\
                        β ⊨ (disj_interp I dnf) /\
                        ~ β ⊨ (conj_interp I cnf)});
      [|generalize cnf,dnf,I;clear s t cnf dnf I;intros].
    - pose proof (normal_form_eq s) as es;
        pose proof (normal_form_eq t) as et;
        rewrite <- dnf_to_cnf_equiv in et.
      rewrite (@dnf_support_incl (sup s) I) in es
        by (apply normal_form_sup||apply incl_appl;reflexivity).
      rewrite (@cnf_support_incl (sup t) I) in et
        by (apply dnf_to_cnf_support ||apply incl_appr;reflexivity).
      apply 𝒜_complete in es,et.
      intros [h|h];[left|right];setoid_rewrite es;setoid_rewrite et;
        apply h.
    - induction dnf as [|d dnf];
        [simpl;left;
         unfold disj_interp;simpl;setoid_rewrite sat_bot;tauto|].
      destruct IHdnf as [h|h].
      + cut ({forall β : clique,
                α ≲ β
                 -> β ⊨ (⋀ (mapNF I d))
                 -> β ⊨ (conj_interp I cnf)}
             +
             {exists β : clique,
                 (α ≲ β) /\
                 β ⊨ (⋀ (mapNF I d))
                 /\ ~ β ⊨ (conj_interp I cnf)}).
        * intros [h'|h'].
          -- left;intros β h1 [h2|h2].
             ++ apply h';simpl;tauto.
             ++ apply h;tauto.
          -- right;destruct h' as (β&h1&h2&h3).
             exists β;split;[|split];auto.
             left;simpl in h2;tauto.
        * clear h.
          induction cnf as [|c cnf];
            [simpl;left;
             unfold conj_interp;simpl;setoid_rewrite sat_top;tauto|].
          destruct IHcnf as [h|h].
          -- cut ({forall β : clique,
                      α ≲ β
                      -> β ⊨ (⋀ (mapNF I d))
                      -> β ⊨ (⋁ (mapNF I c))}
                  +
                  {exists β : clique,
                      (α ≲ β) /\
                      β ⊨ (⋀ (mapNF I d))
                      /\ ~ β ⊨ (⋁ (mapNF I c))}).
             ++ intros [h'|h'].
                ** left;intros β h1 h2;split.
                   --- now apply h'.
                   --- now apply h.
                ** right.
                   destruct h' as (β&h1&h2&h3);exists β.
                   split;[|split];auto.
                   intros (f1&f2).
                   tauto.
             ++ clear h.
                induction I as [|i I];simpl;
                  [right;exists α;split;[reflexivity
                                   |rsimpl;tauto]|].
                destruct (choose_clique_𝖦 (α⇂i)(d i) (c i)) as [hi|hi].
                ** left.
                   intros β h1 (h2&h3).
                   left;apply obs𝖦_to_𝒯_sat, hi,obs𝖦_to_𝒯_sat,h2.
                   intros a ha;simpl;apply h1,ha.
                ** destruct IHI as [h|h].
                   --- left.
                       intros β h1 (h2&h3).
                       now right;apply h.
                   --- right.
                       destruct h as (β&h1&h2&h3).
                       destruct hi as (γ&h4&h5&h6).
                       destruct (auxiliary I h1 h4) as (δ&h7&h8&h9).
                       exists δ;split;[|split;[split|]].
                       *** assumption.
                       *** apply obs𝖦_to_𝒯_sat;rewrite h8;
                             assumption.
                       *** apply satisfies_Meet.
                           rewrite satisfies_Meet in h2.
                           intros x hx;apply in_map_iff in hx
                             as (j&<-&hj).
                           destruct_eqX i j;subst;
                             [apply obs𝖦_to_𝒯_sat;rewrite h8;
                              assumption|].
                           apply obs𝖦_to_𝒯_sat.
                           rewrite h9 by tauto.
                           apply obs𝖦_to_𝒯_sat.
                           apply h2,in_map_iff.
                           exists j;tauto.
                       *** intros [f|f].
                           ---- apply h6;rewrite <- h8.
                                apply obs𝖦_to_𝒯_sat,f.
                           ---- apply satisfies_Join in f
                               as (x&hx&h).
                                apply in_map_iff in hx as (j&<-&hj).
                                destruct_eqX i j;subst;
                                  [apply h6;rewrite <- h8 in *;
                                   apply obs𝖦_to_𝒯_sat,h|].
                                apply h3,satisfies_Join.
                                eexists;split.
                                ++++ apply in_map_iff;exists j.
                                     split;[reflexivity|].
                                     assumption.
                                ++++ rewrite obs𝖦_to_𝒯_sat in *.
                                     rewrite <- h9 by tauto.
                                     assumption.
          -- right.
             destruct h as (β&h).
             exists β.
             repeat (split;[tauto|]).
             intros (h1&h2).
             apply h,h2.
      + right.
        destruct h as (β&h1&h2&h3).
        exists β;split;[|split];auto.
        right;apply h2.
  Qed.
  
End s.

