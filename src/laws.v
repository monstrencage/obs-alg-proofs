Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Import equiv_obs.

(** * Useful laws of Heyting algebras *)

Section s.
  (** * Basic laws *)
  Context {G : Graph}.
  Context {A : relation observation}.
  Notation "A⁺" := (ha_ax (+) A). 
  Remark HA_A s t : s =ha t -> A⁺ ⊢ s ≡ t.
  Proof. intro p;apply eo_ax;left;exact p. Defined.
  Hint Resolve HA_A : core.

  Remark eo_and_ass a b c : A⁺ ⊢ a ⟑ (b ⟑ c) ≡ (a ⟑ b) ⟑ c.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_and_comm a b : A⁺ ⊢ a ⟑ b ≡ b ⟑ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_and_top a : A⁺ ⊢ a ⟑ ⊤o ≡ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_or_ass a b c : A⁺ ⊢ a ⟇ (b ⟇ c) ≡ (a ⟇ b) ⟇ c.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_or_comm a b : A⁺ ⊢ a ⟇ b ≡ b ⟇ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_or_bot a : A⁺ ⊢ a ⟇ ⊥o ≡ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_abs1 a b : A⁺ ⊢ a ⟇ (a ⟑ b) ≡ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_abs2 a b : A⁺ ⊢ a ⟑ (a ⟇ b) ≡ a.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_tauto a : A⁺ ⊢ a → a ≡ ⊤o.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_impl_premise a b : A⁺ ⊢ a ⟑ (a→b) ≡ a ⟑ b.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_impl_concl a b : A⁺ ⊢ b ⟑ (a→b) ≡ b.
  Proof with (auto with equiv_obs). auto... Qed.
  Remark eo_impl_distr a b c : A⁺ ⊢  a → (b ⟑ c) ≡ (a→b) ⟑ (a→c).
  Proof with (auto with equiv_obs). auto... Qed.

  Hint Resolve eo_and_ass eo_and_comm eo_and_top eo_or_ass eo_or_comm
       eo_or_bot eo_abs1 eo_abs2 eo_tauto eo_impl_premise eo_impl_concl
       eo_impl_distr : core.
  
  Remark eo_and_bot a : A⁺ ⊢ a ⟑ ⊥o ≡ ⊥o.
  Proof.
    rewrite <- (eo_abs1 ⊥o a) at 2.
    rewrite eo_or_comm,eo_or_bot.
    apply eo_and_comm.
  Qed.

  Remark eo_or_top a : A⁺ ⊢ a ⟇ ⊤o ≡ ⊤o.
  Proof.
    rewrite <- (eo_abs2 ⊤o a) at 2.
    rewrite eo_and_comm,eo_and_top.
    apply eo_or_comm.
  Qed.

  Remark eo_and_idem a : A⁺ ⊢ a ⟑ a ≡ a.
  Proof with (auto with equiv_obs).
    transitivity (a⟑(a⟇⊥o))...
  Qed.
  
  Remark eo_or_idem a : A⁺ ⊢ a ⟇ a ≡ a.
  Proof with (auto with equiv_obs).
    transitivity (a⟇(a⟑⊤o))...
  Qed.

  Hint Resolve eo_or_idem eo_and_idem eo_or_top eo_and_bot: core.

  (** * [inf_obs A⁺] is a partial order with respect to [equiv_Obs] *)
  Global Instance inf_obs_preorder : PreOrder (inf_obs A⁺).
  Proof with (auto with equiv_obs).
    split.
    - intro;unfold inf_obs;auto.
    - intros a b c e1 e2;unfold inf_obs in *.
      rewrite <- e2,eo_or_ass,e1,e2 at 1...
  Qed.

  Global Instance inf_obs_partialorder :
    PartialOrder (equiv_Obs A⁺) (inf_obs A⁺).
  Proof with (auto with equiv_obs).
    intros a b;split...
    - intro e;split...
      + unfold inf_obs;rewrite e;auto. 
      + unfold Basics.flip,inf_obs;rewrite e;auto.
    - intros (e1&e2);unfold Basics.flip,inf_obs in *.
      rewrite <- e1, <- e2 at 1;auto.
  Qed.

  Remark eq_obs_inf_obs :
    subrelation (equiv_Obs A⁺) (inf_obs A⁺).
  Proof.
    now intros s t E;apply inf_obs_partialorder in E as (h&_).
  Qed.

  Hint Resolve eq_obs_inf_obs : core.

  (** * Lattice properties *)
  Global Instance o_or_inf :
    Proper ((inf_obs A⁺) ==> (inf_obs A⁺) ==> (inf_obs A⁺)) o_or.
  Proof with (auto with equiv_obs).
    intros a b e1 c d e2;unfold inf_obs in *.
    rewrite <- e1,<-e2 at 2.
    repeat rewrite eo_or_ass;apply eo_or...
    repeat rewrite <-eo_or_ass;apply eo_or...
  Qed.
  
  Remark obs_join a b c : A⁺ ⊢ a ≦ c -> A⁺ ⊢ b ≦ c -> A⁺ ⊢ a⟇b ≦ c.
  Proof.
    intros e1 e2;unfold inf_obs in *.
    rewrite <- eo_or_ass,e2,e1;reflexivity.
  Qed.
  Remark eo_inf_o_and a b : A⁺ ⊢ a ≦ b <-> A⁺ ⊢ a ⟑ b ≡ a.
  Proof.
    split;intro e;unfold inf_obs in *.
    - rewrite <- e;auto.
    - rewrite <- e.
      rewrite eo_or_comm,eo_and_comm;auto.
  Qed. 
  Remark obs_meet a b c : A⁺ ⊢ a ≦ b -> A⁺ ⊢ a ≦ c -> A⁺ ⊢ a ≦ b⟑c.
  Proof.
    repeat rewrite eo_inf_o_and.
    intros e1 e2.
    rewrite <-e2 at 2.
    rewrite <- e1 at 2.
    apply eo_and_ass.
  Qed.

  Remark eo_inf_or_l a b : A⁺ ⊢ a ≦ a ⟇ b.
  Proof with (auto with equiv_obs).
    unfold inf_obs;rewrite eo_or_ass;auto...
  Qed.
  Remark eo_inf_or_r a b : A⁺ ⊢ b ≦ a ⟇ b.
  Proof with (auto with equiv_obs).
    unfold inf_obs;rewrite eo_or_comm,<-eo_or_ass;auto...
  Qed.
  Remark eo_inf_and_l a b : A⁺ ⊢ a ⟑ b ≦ a.
  Proof with (auto with equiv_obs).
    apply eo_inf_o_and;rewrite eo_and_comm,eo_and_ass;auto...
  Qed.
  Remark eo_inf_and_r a b : A⁺ ⊢ a ⟑ b ≦ b.
  Proof with (auto with equiv_obs).
    apply eo_inf_o_and;rewrite <-eo_and_ass;auto...
  Qed.

  Hint Resolve eo_inf_or_l eo_inf_or_r eo_inf_and_l eo_inf_and_r : core.

  Remark eo_inf_or_left a c b : A⁺ ⊢ c ≦ a -> A⁺ ⊢ c ≦ a ⟇ b.
  Proof. intros ->;auto. Qed.
  Remark eo_inf_or_right a b c : A⁺ ⊢ c ≦ b -> A⁺ ⊢ c ≦ a ⟇ b.
  Proof. intros ->;auto. Qed.
  Remark eo_inf_and_left a b c : A⁺ ⊢ a ≦ c -> A⁺ ⊢ a ⟑ b ≦ c.
  Proof. intros <-;auto. Qed.
  Remark eo_inf_and_right a b c : A⁺ ⊢ b ≦ c -> A⁺ ⊢ a ⟑ b ≦ c.
  Proof. intros <-;auto. Qed.

  Global Instance o_and_inf :
    Proper ((inf_obs A⁺) ==> (inf_obs A⁺) ==> (inf_obs A⁺)) o_and.
  Proof.
    intros a b e1 c d e2.
    apply obs_meet.
    - transitivity a;auto.
    - transitivity c;auto.
  Qed.

  (** * Properties of the implication *)
  Lemma eo_inf_impl_right_mon a b c : A⁺ ⊢ b ≦ c -> A⁺ ⊢ (a → b) ≦ (a → c).
  Proof.
    intro e;apply eo_inf_o_and.
    apply eo_inf_o_and in e.
    rewrite <- e at 2.
    symmetry;apply eo_impl_distr. 
  Qed.
  Lemma eo_inf_impl_concl a b : A⁺ ⊢ b ≦ a → b.
  Proof. apply eo_inf_o_and,eo_impl_concl. Qed.
  Lemma eo_impl_mp a b : A⁺ ⊢ a ⟑ (a → b) ≦ b.
  Proof. rewrite eo_impl_premise; apply eo_inf_and_r. Qed.
  Lemma eo_inf_o_impl a b : A⁺ ⊢ a ≦ b <-> A⁺ ⊢ ⊤o ≦ a → b.
  Proof.
    symmetry;split;intro e.
    - rewrite <- eo_and_top.
      apply eo_inf_o_and in e.
      rewrite <- e at 1.
      rewrite (eo_and_comm ⊤o),eo_and_top.
      apply eo_impl_mp.
    - rewrite <- (eo_tauto a).
      apply eo_inf_impl_right_mon,e.
  Qed.
  
  Proposition eo_heyting a b c : A⁺ ⊢ a ⟑ b ≦ c <-> A⁺ ⊢ a ≦ b→c.
  Proof.
    split.
    - intros e.
      rewrite <- eo_inf_impl_right_mon by apply e;clear e.
      rewrite eo_impl_distr.
      rewrite eo_tauto,eo_and_top.
      apply eo_inf_impl_concl.
    - intro e.
      apply eo_inf_o_and in e.
      rewrite <- e.
      rewrite <- eo_and_ass.
      rewrite (eo_and_comm _ b).
      rewrite eo_impl_premise.
      rewrite eo_and_ass.
      apply eo_inf_and_r.
  Qed.
  Lemma eo_curry a b c : A⁺ ⊢ (a ⟑ b) → c ≡ a → (b→c).
  Proof.
    apply inf_obs_partialorder;unfold Basics.flip;split.
    - apply eo_heyting.
      rewrite <- eo_heyting.
      repeat rewrite <- eo_and_ass.
      rewrite eo_and_comm,eo_impl_premise.
      auto.
    - apply eo_heyting.
      rewrite eo_and_ass.
      rewrite (eo_and_comm _ a).
      rewrite eo_impl_mp.
      rewrite (eo_and_comm _ b).
      apply eo_impl_mp.
  Qed.

  Global Instance o_impl_inf :
    Proper (Basics.flip (inf_obs A⁺) ==> (inf_obs A⁺) ==> (inf_obs A⁺))
           o_impl.
  Proof.
    unfold Basics.flip;intros a b e1 c d e2.
    apply eo_heyting.
    rewrite e1,<-e2,eo_and_comm.
    apply eo_impl_mp.
  Qed.
  
  (** * Additional laws *)
  Lemma eo_distr1 a b c : A⁺ ⊢ a ⟇ (b ⟑ c) ≡ (a ⟇ b) ⟑ (a ⟇ c).
  Proof.
    apply inf_obs_partialorder;unfold Basics.flip;split.
    - apply obs_join;apply obs_meet;auto.
      + transitivity b;auto.
      + transitivity c;auto.
    - apply eo_heyting,obs_join.
      + apply eo_heyting.
        rewrite eo_abs2;auto.
      + apply eo_heyting.
        rewrite eo_and_comm at 1.
        apply eo_heyting,obs_join.
        * apply eo_heyting.
          transitivity  a;auto.
        * apply eo_heyting.
          rewrite eo_and_comm at 1.
          auto.
  Qed.
  Lemma eo_distr2 a b c : A⁺ ⊢ a ⟑ (b ⟇ c) ≡ (a ⟑ b) ⟇ (a ⟑ c).
  Proof.
    apply inf_obs_partialorder;unfold Basics.flip;split.
    - rewrite eo_and_comm at 1.
      apply eo_heyting,obs_join;apply eo_heyting;
        rewrite eo_and_comm at 1;auto.
    - apply obs_join;apply obs_meet;auto.
      + transitivity b;auto.
      + transitivity c;auto.
  Qed.

  Lemma eo_impl_distr_left a b c : A⁺ ⊢ (a ⟇ b) → c ≡ (a → c) ⟑ (b→c).
  Proof.
    apply inf_obs_partialorder;unfold Basics.flip;split.
    - apply obs_meet.
      + apply o_impl_inf;unfold Basics.flip;simpl;reflexivity||auto.
      + apply o_impl_inf;unfold Basics.flip;simpl;reflexivity||auto.
    - apply eo_heyting.
      rewrite <- eo_curry.
      rewrite eo_distr2.
      rewrite (eo_and_comm _ b).
      rewrite eo_impl_premise.
      apply eo_heyting.
      rewrite eo_distr2.
      apply obs_join.
      + rewrite eo_and_ass.
        apply eo_heyting;auto.
      + rewrite eo_and_ass.
        auto.
  Qed.
  Lemma eo_inf_top a : A⁺ ⊢ a ≦ ⊤o.
  Proof. apply eo_inf_o_and,eo_and_top. Qed.
  Lemma eo_inf_bot a : A⁺ ⊢ ⊥o ≦ a.
  Proof. unfold inf_obs;rewrite eo_or_comm;apply eo_or_bot. Qed.
  Lemma eo_eq_top_iff_top_inf a : A⁺ ⊢ a ≡ ⊤o <-> A⁺ ⊢ ⊤o ≦ a.
  Proof.
    split.
    - intros ->;reflexivity.
    - intro;apply inf_obs_partialorder;split.
      + apply eo_inf_top.
      + assumption.
  Qed.
  Lemma eo_eq_bot_iff_inf_bot a : A⁺ ⊢ a ≡ ⊥o <-> A⁺ ⊢ a ≦ ⊥o.
  Proof.
    split.
    - intros ->;reflexivity.
    - intro;apply inf_obs_partialorder;split.
      + assumption.
      + apply eo_inf_bot.
  Qed.
  Lemma eo_contradict s : A⁺ ⊢ s ⟑ (s → ⊥o) ≡ ⊥o.
  Proof.
    apply eo_eq_bot_iff_inf_bot.
    rewrite eo_and_comm.
    apply eo_heyting;reflexivity.
  Qed.
  Remark eo_top_impl s : A⁺ ⊢ (⊤o → s) ≡ s.
  Proof.
    rewrite <- eo_and_top, eo_and_comm,eo_impl_premise,eo_and_comm,
      eo_and_top.
    reflexivity.
  Qed.

  (** * [n]-ary meets and joins *)
  Remark obs_Meet a X : (forall b, b ∈ X -> A⁺ ⊢ a ≦ b) -> A⁺ ⊢ a ≦ ⋀ X.
  Proof with (auto with equiv_obs).
    induction X as [|α X];simpl;auto.
    - intros _;apply eo_inf_o_and;auto.
    - intros h.
      transitivity (a⟑a);[|apply o_and_inf];auto...
  Qed.

  Remark obs_Join a X : (forall b, b ∈ X -> A⁺ ⊢ b ≦ a) -> A⁺ ⊢ ⋁ X ≦ a.
  Proof with (auto with equiv_obs).
    induction X as [|α X];simpl;auto.
    - intros _;apply eo_inf_o_and;auto.
      rewrite eo_and_comm;auto.
    - intros h.
      transitivity (a⟇a);[apply o_or_inf|];auto...
  Qed.

  Remark Join_app X Y : A⁺ ⊢ ⋁ (X++Y) ≡ ⋁ X ⟇ ⋁ Y.
  Proof with (auto with equiv_obs).
    induction X;simpl.
    - rewrite eo_or_comm;auto...
    - rewrite IHX;auto...
  Qed.
  Remark Meet_app X Y : A⁺ ⊢ ⋀ (X++Y) ≡ ⋀ X ⟑ ⋀ Y.
  Proof with (auto with equiv_obs).
    induction X;simpl.
    - rewrite eo_and_comm;auto...
    - rewrite IHX;auto...
  Qed.

  Remark eo_inf_in_Join a X : a ∈ X -> A⁺ ⊢ a ≦ ⋁ X.
  Proof.
    intro I;apply in_split in I as (B&C&->);rewrite Join_app;simpl.
    rewrite eo_or_comm,<- eo_or_ass;apply eo_inf_or_l.
  Qed.
  Remark eo_inf_in_Meet a X : a ∈ X -> A⁺ ⊢ ⋀ X ≦ a.
  Proof.
    intro I;apply in_split in I as (B&C&->);rewrite Meet_app;simpl.
    rewrite eo_and_comm,<- eo_and_ass;apply eo_inf_and_l.
  Qed.

  Lemma and_Join a X : A⁺ ⊢ a ⟑ ⋁ X ≡ ⋁ (map (fun b => a ⟑ b) X).
  Proof.
    induction X;simpl;[now auto|].
    rewrite<-IHX;auto.
    apply eo_distr2.
  Qed.

  Lemma or_Meet a X : A⁺ ⊢ a ⟇ ⋀ X ≡ ⋀ (map (fun b => a ⟇ b) X).
  Proof.
    induction X;simpl;[now auto|].
    rewrite<-IHX;auto.
    apply eo_distr1.
  Qed.
  
  Lemma Join_and_Join X Y :
    A⁺ ⊢ ⋁ X ⟑ ⋁ Y ≡ ⋁ (map (fun p => fst p ⟑ snd p) (pairs X Y)).
  Proof with (auto with equiv_obs).
    induction X;simpl;auto.
    - rewrite eo_and_comm;auto.
    - rewrite eo_and_comm,eo_distr2.
      rewrite (eo_and_comm _ (⋁ X)).
      rewrite map_app,Join_app.
      rewrite <- IHX.
      rewrite map_map;simpl.
      apply eo_or;auto...
      rewrite <- and_Join;auto...
  Qed.

  Lemma Meet_or_Meet X Y :
    A⁺ ⊢ ⋀ X ⟇ ⋀ Y ≡ ⋀ (map (fun p => fst p ⟇ snd p) (pairs X Y)).
  Proof with (auto with equiv_obs).
    induction X;simpl;auto.
    - rewrite eo_or_comm;auto.
    - rewrite eo_or_comm,eo_distr1.
      rewrite (eo_or_comm _ (⋀ X)).
      rewrite map_app,Meet_app.
      rewrite <- IHX.
      rewrite map_map;simpl.
      apply eo_and;auto...
      rewrite <- or_Meet;auto...
  Qed.

  Instance Meet_monotone :
    Proper (@incl observation ==> Basics.flip (inf_obs A⁺)) ⋀.
  Proof.
    unfold Basics.flip;intros l m;induction l;simpl;intros hl.
    - unfold inf_obs;auto.  
    - apply incl_cons_inv in hl as (ha&hl).
      apply IHl in hl.
      apply obs_meet;auto.
      apply eo_inf_in_Meet,ha.
  Qed.
  Instance Join_monotone : Proper (@incl observation ==> (inf_obs A⁺)) ⋁.
  Proof.
    intros l m;induction l;simpl;intros hl.
    - unfold inf_obs;rewrite eo_or_comm;auto.  
    - apply incl_cons_inv in hl as (ha&hl).
      apply obs_join;auto.
      apply eo_inf_in_Join,ha.
  Qed.
  Instance Meet_equiv :
    Proper (@equivalent observation ==> equiv_Obs A⁺) ⋀.
  Proof.
    intros X Y E;apply inf_obs_partialorder;unfold Basics.flip;split;
      apply Meet_monotone;rewrite E;reflexivity.
  Qed.
  Instance Join_equiv :
    Proper (@equivalent observation ==> equiv_Obs A⁺) ⋁.
  Proof.
    intros X Y E;apply inf_obs_partialorder;unfold Basics.flip;split;
      apply Join_monotone;rewrite E;reflexivity.
  Qed.

  
  Lemma Meet_map_equiv_pointwise {X Ax} f g l :
    (forall x : X, x ∈ l -> Ax ⊢ f x ≡ g x) ->
    Ax ⊢ ⋀ (map f l) ≡ ⋀ (map g l).
  Proof.
    clear.
    induction l;simpl;[reflexivity|].
    intro h;rewrite (h a) by now left.
    rewrite IHl by (intros;apply h;now right).
    reflexivity.
  Qed.

  Lemma flat_map_Meet {X}:
    forall f (l : list X), A⁺ ⊢ ⋀ (flat_map f l) ≡ ⋀ (map ⋀ (map f l)).
  Proof.
    intro f;induction l;simpl;[reflexivity|].
    rewrite <- IHl;apply Meet_app.
  Qed.

  Lemma Join_map_equiv_pointwise {X Ax} f g l :
    (forall x : X, x ∈ l -> Ax ⊢ f x ≡ g x) ->
    Ax ⊢ ⋁ (map f l) ≡ ⋁ (map g l).
  Proof.
    clear.
    induction l;simpl;[reflexivity|].
    intro h;rewrite (h a) by now left.
    rewrite IHl by (intros;apply h;now right).
    reflexivity.
  Qed.

  Lemma flat_map_Join {X} :
    forall f (l : list X), A⁺ ⊢ ⋁ (flat_map f l) ≡ ⋁ (map ⋁ (map f l)).
  Proof.
    intro f;induction l;simpl;[reflexivity|].
    rewrite <- IHl;apply Join_app.
  Qed.
  Lemma eo_impl_Join u s :
    A⁺ ⊢ ⋁ u → s ≡ ⋀ (map (fun x => x → s) u).
  Proof.
    induction u as [|a u];simpl.
    - apply eo_eq_top_iff_top_inf,eo_heyting.
      rewrite eo_and_bot.
      apply eo_inf_bot.
    - rewrite eo_impl_distr_left.
      rewrite IHu.
      reflexivity.
  Qed.
  Corollary impl_Join u s :
    A⁺ ⊢ ⋁ (map o_obs u) → s ≡ ⋀ (map (fun a => ⦑a⦒ → s) u).
  Proof.
    etransitivity;[apply eo_impl_Join|].
    rewrite map_map;reflexivity.
  Qed.
  
  Lemma eo_Meet_impl u s :
    A⁺ ⊢ s → ⋀ u ≡ ⋀ (map (fun x => s → x) u).
  Proof.
    induction u as [|a u];simpl.
    - apply eo_eq_top_iff_top_inf,eo_heyting.
      rewrite eo_and_comm,eo_and_top.
      apply eo_inf_top.
    - rewrite eo_impl_distr.
      rewrite IHu.
      reflexivity.
  Qed.
  Corollary Meet_impl u s :
    A⁺ ⊢ s → ⋀ (map o_obs u) ≡ ⋀ (map (fun a => s → ⦑a⦒) u).
  Proof.
    etransitivity;[apply eo_Meet_impl|].
    rewrite map_map;reflexivity.
  Qed.

  (** * Finite and singleton cliques *)
  Context {decG : DecidableGraph G}.
  
  Global Instance π_proper : Proper (inf_fcliques ==> (inf_obs A⁺)) π.
  Proof.
    intros α β;unfold π;intros h.
    apply obs_Meet;intros x hx;apply in_map_iff in hx as (a&<-&ha).
    apply h in ha;apply eo_inf_in_Meet,in_map_iff;exists a;tauto.
  Qed.

  Remark var_clique a : A⁺ ⊢ π (sgl__f a) ≡ ⦑a⦒.
  Proof. unfold π;simpl;auto. Qed.

End s.

Ltac split_order :=
  apply inf_obs_partialorder;unfold Basics.flip;split.
Ltac unfold__lat :=
  repeat apply obs_meet || apply obs_join
  ||((apply obs_Join||apply obs_Meet);
    let x := fresh "x" in
    let hx := fresh "hx" in
    let a := fresh "a" in
    let ha := fresh "ha" in
    intros x hx;apply in_map_iff in hx as (a&<-&ha)).
Ltac unfold_meet :=
  apply obs_Meet;
  let x := fresh "x" in
  let hx := fresh "hx" in
  let a := fresh "a" in
  let ha := fresh "ha" in
  intros x hx;apply in_map_iff in hx as (a&<-&ha).
Ltac unfold_join :=
  apply obs_Join;
  let x := fresh "x" in
  let hx := fresh "hx" in
  let a := fresh "a" in
  let ha := fresh "ha" in
  intros x hx;apply in_map_iff in hx as (a&<-&ha).

Global Hint Resolve eo_or_idem eo_and_idem eo_or_top eo_and_bot
       eo_inf_or_l eo_inf_or_r eo_inf_and_l eo_inf_and_r
       eo_and_ass eo_and_comm eo_and_top eo_or_ass eo_or_comm
       eo_or_bot eo_abs1 eo_abs2 eo_tauto eo_impl_premise eo_impl_concl
       eo_impl_distr : equiv_obs.
