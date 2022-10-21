Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations Bool.
Require Import decidable_prop.
Require Import list_dec.

(** * Main definitions *)
Class Graph :=
  { 
  vertex : Set ;
  coh : relation vertex ;
  coh_refl :> Reflexive coh;
  coh_sym :> Symmetric coh
  }.


Section s.
  Context {G : Graph}.
  Infix " ⁐ " := coh (at level 40).

  Definition incoh : relation vertex := fun a b => ~ a ⁐ b.
  Infix " ⌣ " := incoh (at level 40).

  Global Instance incoh_irrefl : Irreflexive incoh.
  Proof. intros x h;apply h;reflexivity. Qed.

  Global Instance incoh_sym : Symmetric incoh.
  Proof. intros x y h1 h2;apply h1;symmetry;assumption. Qed.

  Class clique : Set :=
    {
      member : vertex -> bool;
      incompat : vertex -> option vertex;
      members_are_coh :
      forall a b, Is_true (member a) -> Is_true (member b) -> a ⁐ b;
      incompat_Some :
      forall a b, incompat a = Some b -> Is_true (member b) /\ a ⌣ b;
      incompat_None :
      forall a b, incompat a = None -> Is_true (member b) -> a ⁐ b;
      non_empty : exists a : vertex, member a = true    
    }.

  Arguments member α a : rename, clear implicits. 
  Arguments incompat α a : rename, clear implicits. 

  Arguments members_are_coh α : rename, clear implicits. 
  Arguments incompat_Some α : rename, clear implicits. 
  Arguments incompat_None { α a b}: rename.

  Notation " u ⋊ x " := (exists b, (incompat x u) = Some b) (at level 20).
  Notation " u ∝ x " := (incompat x u = None) (at level 20).

  Global Instance satClique : Satisfaction vertex clique :=
    (fun u x => Is_true (member x u)).
  
  (** Vertex compatibility *)
  Lemma incompat_are_incoh a α :
    a ⋊ α <-> exists b, b ⊨ α /\ a ⌣ b.
  Proof.
    split.
    - intros (b&hb);exists b;apply incompat_Some,hb.
    - intros (b&h1&h2);case_eq (incompat α a);[eauto|].
      intros f;exfalso.
      apply h2,(incompat_None f),h1.
  Qed.

  Lemma compat_are_coh a α :
    a ∝ α <-> forall b, b ⊨ α -> a ⁐ b.
  Proof.
    split.
    - intros h b;apply (incompat_None h).
    - intros h;case_eq (incompat α a);[|reflexivity].
      intros b hb;apply incompat_Some in hb as (h1&h2).
      exfalso;apply h2,h,h1.
  Qed.

  Global Instance incompat_dec a α : DecidableProp (a ⋊ α).
  Proof.
    case_eq (incompat α a);intros;
      [left;eauto|right;intros (?&F);discriminate].
  Qed.

  Global Instance compat_dec a α : DecidableProp (a ∝ α).
  Proof.
    case_eq (incompat α a);intros;
      [right;discriminate|left;reflexivity]. 
  Qed.

  (** Comparing cliques *)
  Notation inf_cliques := (fun a b => b ≲ a).
  Infix " ⊃ " := inf_cliques (at level 20).
 
  Lemma inf_clique_compat α β :
    α ⊃ β -> forall a, a ⋊ β -> a ⋊ α.
  Proof.
    intros h1 a (b&h2).
    apply incompat_Some in h2 as (h2&h3).
    case_eq (incompat α a);[eauto|intro h4;exfalso].
    apply h3,(incompat_None h4),h1,h2.
  Qed.


  (** Incompatibility between cliques *)
  Definition incompatible : relation clique :=
    fun x y => exists a b, a ⊨ x /\ b ⊨ y /\ a ⌣ b.

  Infix " ↯ " := incompatible (at level 50).

  Remark incompatible_incompat α β :
    α ↯ β <-> exists a, a ⊨ α /\ a ⋊ β.
  Proof.
    split.
    - intros (a&b&h1&h2&h3);exists a;split;[assumption|].
      apply incompat_are_incoh;exists b;split;assumption.
    - intros (a&h1&h2).
      apply incompat_are_incoh in h2 as (b&h2&h3).
      exists a, b;tauto.
  Qed.
      
  Global Instance irrefl_incompatible : Irreflexive incompatible.
  Proof.
    intros x (a&b&ha&hb&hab).
    apply hab,(members_are_coh x);assumption.
  Qed.

  Global Instance sym_incompatible : Symmetric incompatible.
  Proof.
    intros x y (a&b&ha&hb&hab);exists b,a;repeat split;auto.
    symmetry;assumption.
  Qed.

  Global Instance incompatible_inf :
    Proper (inf_cliques ==> inf_cliques ==> Basics.flip Basics.impl)
           incompatible.
  Proof.
    intros x x' hx y y' hy (a&b&ha&hb&h).
    exists a,b;repeat split;[apply hx|apply hy|];auto.
  Qed.
  
  Global Instance incompatible_eq :
    Proper (sequiv ==> sequiv ==> iff) incompatible.
  Proof.
    intros x x' hx y y' hy.
    split;intros (a&b&h1&h2&h3);
      exists a,b;(split;[apply hx|split;[apply hy|]]);assumption.
  Qed.

  (* (** The empty clique *) *)
  (* Definition empt : clique. *)
  (* Proof. *)
  (*   exists (fun _ => false) (fun _ => None). *)
  (*   - intros a b h;simpl in h;exfalso;exact h. *)
  (*   - discriminate. *)
  (*   - unfold Is_true;tauto.  *)
  (* Defined. *)
  
  (* Lemma empt_spec a : ~ a ⊨ empt. *)
  (* Proof. simpl;tauto. Qed. *)
  (* Opaque empt. *)

  (* Remark empt_max x : x ⊃ empt. *)
  (* Proof. intros a h;exfalso;apply (@empt_spec a h). Qed. *)

  (** Union of cliques *)
  Definition joins (x y z : clique) :=
    forall a, a ⊨ z <-> a ⊨ x \/ a ⊨ y.

  Global Instance joins_proper :
    Proper (sequiv ==> sequiv ==> sequiv ==> iff) joins.
  Proof.
    intros x x' Ex y y' Ey z z' Ez;unfold joins.
    setoid_rewrite (Ex _).
    setoid_rewrite (Ey _).
    setoid_rewrite (Ez _).
    reflexivity.
  Qed.

End s.
Infix " ⁐ " := coh (at level 40).
Infix " ⌣ " := incoh (at level 40).
Arguments member {G} α a : rename. 
Arguments incompat {G} α a : rename.

Notation " u ⋊ x " := (exists b, (incompat x u) = Some b) (at level 20).
Notation " u ∝ x " := (incompat x u = None) (at level 20).
Infix " ↯ " := incompatible (at level 50).

Arguments members_are_coh {G} α : rename.  
Arguments incompat_are_incoh {G} α : rename.
Arguments incompat_Some α : rename, clear implicits. 
Arguments incompat_None { α a b}: rename.

Notation inf_cliques := (fun a b => b ≲ a).
Infix " ⊃ " := inf_cliques (at level 20).

(** * Decidable Graphs *)
Class DecidableGraph G :=
  {
    decidable_vertex :> decidable_set (@vertex G);
    decidale_coh :> forall u v, DecidableProp (u ⁐ v)
  }.

Section decidable_graph.
  
  Context { G : Graph } {decG : DecidableGraph G}.

  Global Instance decidable_incoh u v : DecidableProp (u ⌣ v).
  Proof.  unfold incoh;typeclasses eauto. Qed.
  
  Lemma not_incompatible_is_joins x y : ~ x ↯ y <-> exists z, joins x y z.
  Proof.
    split.
    - unfold joins, incompatible.
      intro hxy;set (memz:= fun a => member x a || member y a).
      set (incompatz := fun a =>
                          match incompat x a, incompat y a with
                          | Some b,_
                          | None,Some b => Some b
                          | None,None => None
                          end).
      assert
        ((forall a b, Is_true (memz a) -> Is_true (memz b) -> a ⁐ b)
         /\ ((forall a b, incompatz a = Some b -> Is_true (memz b) /\ a ⌣ b)
         /\ (forall a b,incompatz a = None -> Is_true (memz b)  -> a ⁐ b))
         /\ (exists a, memz a = true))
        as (memok&(iS&iN)&ne).
      + split;[|split].
        * intros a b;unfold memz;clear memz;
            repeat rewrite orb_prop_iff;intros [ha|ha] [hb|hb].
          -- now apply (members_are_coh x).
          -- case_prop (a ⁐ b);[tauto|].
             exfalso;apply hxy;exists a,b;tauto.
          -- symmetry;case_prop (b ⁐ a);[tauto|].
             exfalso;apply hxy;exists b,a;tauto.
          -- now apply (members_are_coh y).
        * split; intros a b;unfold incompatz;clear incompatz;
            unfold memz;clear memz;rewrite orb_prop_iff;
              (case_eq (incompat x a);[|case_eq (incompat y a)]);
              try discriminate.
          -- intros c h e;inversion e;subst;clear e.
             apply incompat_Some in h;tauto.
          -- intros c h _ e;inversion e;subst;clear e.
             apply incompat_Some in h;tauto.
          -- intros h1 h2 _ [h3|h3].
             ++ apply (incompat_None _ h2),h3.
             ++ apply (incompat_None _ h1),h3.
        * destruct (@non_empty _ x) as (a&h).
          exists a;unfold memz;rewrite h;reflexivity.
      + set (z := Build_clique memok iS iN ne).
        exists z;intro a;unfold satisfies at 1,satClique,member;simpl;
          unfold memz.
        rewrite orb_prop_iff.
        tauto.
    - intros (z&hz) (a&b&ha&hb&hab).
      apply hab,(members_are_coh z);apply hz;tauto.
  Qed.
  
  Lemma joins_is_meet x y z :
    joins x y z <-> (z ⊃ x /\ z ⊃ y /\ forall t, t ⊃ x -> t ⊃ y -> t ⊃ z).
  Proof.
    split.
    - intros hj;split;[|split].
      + intros a ha;apply hj;tauto.
      + intros a ha;apply hj;tauto.
      + intros t ht1 ht2 a ha;apply hj in ha as [ha|ha];
          [apply ht1|apply ht2];assumption.
    - intros (h1&h2&hm).
      cut (~ x ↯ y).
      + rewrite not_incompatible_is_joins.
        intros (z'&hz').
        intros a;split.
        * intros h.
          apply hz',hm,h.
          -- intros b hb;apply hz';tauto.
          -- intros b hb;apply hz';tauto.
        * intros [h|h];[apply h1|apply h2];apply h.
      + intros (a&b&h3&h4&h5).
        apply h5,(members_are_coh z);[apply h1|apply h2];assumption.
  Qed.
  
End decidable_graph.
(** * Finite cliques *)
Section finite_cliques.
  Context { G : Graph } {decG : DecidableGraph G}.

  Definition is_coherent (α : list vertex) :=
    forall a b, a ∈ α -> b∈α -> a ⁐ b. 

  Global Instance decidable_is_coherent α :
    DecidableProp (is_coherent α).
  Proof.
    unfold is_coherent.
    assert (d: DecidableProp (forall a, a ∈ α -> forall b, b∈α -> a ⁐ b))
      by typeclasses eauto.
    destruct d as [d|d];[left|right];intros;
      [apply d|intro d';apply d;intros];auto.
  Qed.

  Definition fcliques :=
    { α : list vertex | test (is_coherent α /\ α <> []) = true}.

  Remark fcliques_coherent (α : fcliques) : is_coherent ($α).
  Proof.
    destruct α as (α&h);simpl.
    rewrite test_spec in h;apply h.
  Qed.
  Remark fcliques_non_empty (α : fcliques) : $α <> [].
  Proof.
    destruct α as (α&h);simpl.
    rewrite test_spec in h;apply h.
  Qed.

  Arguments fcliques_coherent : clear implicits.

  (** Comparing finite cliques *)

  Notation inf_fcliques := (fun a b : fcliques => $ b ⊆ $ a).
  Infix " ⊃f " := inf_fcliques (at level 20).
  Notation eq_fcliques := (fun a b : fcliques => $ a ≈ $ b).

  (** From finite cliques to cliques *)
  Definition fcmem (α : fcliques) := fun a => inb a $α.

  Lemma fcmem_coh α a b :
    Is_true (fcmem α a) -> Is_true (fcmem α b) -> a ⁐ b.
  Proof.
    destruct α as (l&h);unfold fcmem;simpl in *;rewrite test_spec in h.
    repeat rewrite Is_true_iff_eq_true,inb_spec;apply h.
  Qed.

  Definition fcic (α : fcliques) :=
    fun a => match (fun b => test (a ⌣ b)):> $α with
          | [] => None
          | b::_ => Some b
          end.
  
  Lemma fcic_Some α a b :
    fcic α a = Some b -> Is_true (fcmem α b) /\ a ⌣ b.
  Proof.
    unfold fcmem, fcic.
    destruct α as (l&h);simpl in *;rewrite test_spec in h.
    case_eq ((fun b0 : vertex => test (a ⌣ b0)) :> l).
    - discriminate.
    - intros c m e E;inversion E;subst;clear E.
      cut (b ∈ ((fun b0 : vertex => test (a ⌣ b0)) :> l));
        [|rewrite e;now left].
      rewrite filter_In.
      rewrite test_spec,Is_true_iff_eq_true,inb_spec.
      tauto.  
  Qed.
  Lemma fcic_None α a b :
    fcic α a = None -> Is_true (fcmem α b) -> a ⁐ b.
  Proof.
    unfold fcmem, fcic.
    destruct α as (l&h);simpl in *;rewrite test_spec in h.
    case_eq ((fun b0 : vertex => test (a ⌣ b0)) :> l).
    - intros e _.
      rewrite filter_nil in e.
      setoid_rewrite <- not_true_iff_false in e.
      setoid_rewrite test_spec in e.
      rewrite Is_true_iff_eq_true,inb_spec.
      intros h';apply e in h'.
      case_prop (a ⁐ b);tauto.
    - discriminate.
  Qed.
  Lemma fc_ne α : exists a, fcmem α a = true.
  Proof.
    unfold fcmem, fcic.
    destruct α as (l&h);simpl in *;rewrite test_spec in h.
    destruct h as (_&h); destruct l as [|a l];[tauto|].
    exists a;simpl;rewrite eqX_refl;reflexivity.
  Qed.
  
  Definition fc_to_clique (α : fcliques) : clique
    := Build_clique (@fcmem_coh α) (@fcic_Some α) (@fcic_None α)
                    (@fc_ne α).
        
  Notation " ! " := fc_to_clique.

  Lemma fc_to_clique_spec a α : a ⊨ (! α) <-> a ∈ $ α.
  Proof.
    unfold fc_to_clique,satisfies,satClique,fcmem;simpl.
    now rewrite Is_true_iff_eq_true,inb_spec.
  Qed.

  Ltac simpl_fc :=
    repeat (rewrite fc_to_clique_spec in *).
  Opaque fc_to_clique.
    
  Global Instance fc_to_clique_proper :
    Proper (inf_fcliques ==> inf_cliques) fc_to_clique.
  Proof.
    intros l m h a;simpl;repeat rewrite fc_to_clique_spec;apply h.
  Qed.
  
  Global Instance fc_to_clique_proper_eq :
    Proper (eq_fcliques ==> sequiv) fc_to_clique.
  Proof. intros l m h a;simpl;simpl_fc;apply h. Qed.

  Remark fc_to_clique_iff α β : α ⊃f β <-> ! α ⊃ ! β.
  Proof.
    autounfold;unfold ssmaller.
    setoid_rewrite fc_to_clique_spec;reflexivity.
  Qed.

  (** Incompatibility between finite cliques *)
  Definition fincompatible (x y : fcliques) :=
    exists a b, a ∈ $x /\ b ∈ $y /\ a ⌣ b.
  Infix " ↯↯ " := fincompatible (at level 50).

  Lemma fincompatible_incompatible x y :
    x ↯↯ y <-> ! x ↯ ! y.
  Proof.
    unfold incompatible,fincompatible;simpl.
    setoid_rewrite Is_true_iff_eq_true;setoid_rewrite inb_spec.
    reflexivity.
  Qed.
  
  Global Instance irrefl_fincompatible : Irreflexive fincompatible.
  Proof.
    intros x h;eapply irrefl_incompatible,fincompatible_incompatible, h.
  Qed.

  Global Instance sym_fincompatible : Symmetric fincompatible.
  Proof. 
    intros x y (a&b&ha&hb&hab);exists b,a;repeat split;auto.
    symmetry;assumption.
  Qed.

  Global Instance fincompatible_inf :
    Proper (inf_fcliques ==> inf_fcliques ==> Basics.flip Basics.impl)
           fincompatible.
  Proof.
    intros x x' hx y y' hy (a&b&ha&hb&h).
    exists a,b;split;[apply hx|split;[apply hy|]];assumption.
  Qed.
  
  Global Instance fincompatible_eq :
    Proper (eq_fcliques ==> eq_fcliques ==> iff) fincompatible.
  Proof.
    intros x x' hx y y' hy.
    apply ssmaller_PartialOrder in hx,hy.
    split;apply fincompatible_inf;apply hx||apply hy.
  Qed.

  Global Instance decidable_incompatible_f x y :
    DecidableProp (x ↯↯ y).
  Proof.
    unfold incompatible;simpl.
    cut (DecidableProp (exists a, a ∈ $ x /\ exists b, b ∈ $ y /\ a ⌣ b)).
    - intro p;eapply DecidableProp_equiv_prop;[apply p|].
      split.
      + intros (a&?&b&?&?);exists a,b;tauto.
      + intros (a&b&h);exists a;split;[|exists b];tauto.
    - typeclasses eauto.
  Qed.

  (** Union of finite cliques *)
  Definition fjoins (x y z : fcliques) := ($ z ≈ $ x ++ $y).

  Global Instance fjoins_proper :
    Proper (eq_fcliques ==> eq_fcliques ==> eq_fcliques ==> iff) fjoins.
  Proof.
    intros x x' Ex y y' Ey z z' Ez;unfold fjoins.
    rewrite Ex,Ey,Ez;reflexivity.
  Qed.
   
  Lemma fjoins_iff_joins x y z :
    fjoins x y z <-> joins (! x) (! y) (! z).
  Proof.
    unfold fjoins,joins;simpl.
    unfold equivalent;setoid_rewrite in_app_iff.
    setoid_rewrite fc_to_clique_spec.
    reflexivity.
  Qed.
  
  Lemma joins_is_meet_f x y z :
    fjoins x y z <-> (z ⊃f x /\ z ⊃f y /\ forall t, t ⊃f x -> t ⊃f y -> t ⊃f z).
  Proof.
    rewrite fjoins_iff_joins,joins_is_meet.
    setoid_rewrite <- fc_to_clique_iff.
    split;intros (h1&h2&h3);(split;[apply h1|split;[apply h2|]]);
      intros t ht1 ht2.
    - apply fc_to_clique_iff,h3;apply fc_to_clique_iff;assumption.
    - cut (is_coherent ($x ++ $y) /\ (($x++$y)<>[]));[|split].
      + intro c;apply test_spec in c.
        replace ($ x ++ $y) with ($(exist _ ($x++$y) c:fcliques))
          by reflexivity.
        set (X := exist _ _ c : fcliques).
        transitivity (!X).
        * apply fc_to_clique_iff,h3;intros a;unfold X;simpl;
            rewrite in_app_iff;tauto.
        * intro a;rewrite fc_to_clique_spec.
          unfold X;simpl;rewrite in_app_iff.
          intros [h|h].
          -- apply ht1,fc_to_clique_spec,h.
          -- apply ht2,fc_to_clique_spec,h.
      + intros a b;repeat rewrite in_app_iff;intros ha hb.
        apply (fcliques_coherent z).
        * destruct ha as [ha|ha];apply h1,ha||apply h2,ha.
        * destruct hb as [hb|hb];apply h1,hb||apply h2,hb.
      + case_eq ($x);[|intros;simpl;discriminate].
        intros f _;revert f;apply fcliques_non_empty. 
  Qed.
  
  Lemma not_incompatible_is_joins_f x y :
    ~ x ↯↯ y <-> exists z : fcliques, fjoins x y z.
  Proof.
    unfold fjoins;split.
    - intro F.
      cut (is_coherent ($x ++ $y) /\ (($x++$y)<>[]));[|split].
      + intro c;apply test_spec in c;exists (exist _ ($x ++ $y) c);
          reflexivity.
      + intros a b h1 h2.
        case_prop (a ⁐ b);[tauto|exfalso].
        apply in_app_iff in h1 as [h1|h1];
          apply in_app_iff in h2 as [h2|h2].
        * apply hyp,(fcliques_coherent x a b);assumption.
        * apply F.
          exists a,b;simpl;repeat rewrite Is_true_iff_eq_true,inb_spec.
          repeat split;auto.
        * apply F.
          exists b,a;simpl;repeat rewrite Is_true_iff_eq_true,inb_spec.
          repeat split;auto.
          symmetry;assumption.
        * apply hyp,(fcliques_coherent y a b);assumption.
      + case_eq ($x);[|intros;simpl;discriminate].
        intros f _;revert f;apply fcliques_non_empty. 
    - intros (z&Ez) (a&b&ha&hb&i);simpl in *.
      apply i,(fcliques_coherent z a b);assumption||(apply Ez,in_app_iff);
        tauto.
  Qed.
  
  Lemma incompatible_or_joins_f x y :
    {x ↯↯ y} + {exists z, fjoins x y z}.
  Proof.
    case_prop (x ↯↯ y);auto.
    right;apply not_incompatible_is_joins_f,hyp.
  Qed.

  Lemma decidable_incompatible_with_fcliques x α :
    DecidableProp (x ↯ ! α).
  Proof.
    case_prop (exists a, a ∈ $ α /\ a ⋊ x).
    - left.
      destruct hyp as (a&ha&hyp).
      apply incompat_are_incoh in hyp as (b&hb&hyp).
      exists b, a;repeat split;auto;simpl_fc;[|symmetry];assumption.
    - right;intros (a&b&ha&hb&i);apply hyp.
      revert ha hb.
      simpl_fc.
      exists b;split;[assumption|].
      apply incompat_are_incoh; exists a;split;[|symmetry];assumption.
  Qed.

  (* (** Projections *) *)

  (* Definition project_list : list vertex -> clique -> list vertex := *)
  (*   fun l x => member x :> l. *)

  (* Lemma is_coherent_project_list l x : is_coherent (project_list l x). *)
  (* Proof. *)
  (*   unfold project_list;intros a b;repeat rewrite filter_In. *)
  (*   repeat rewrite <- Is_true_iff_eq_true. *)
  (*   intros;apply (members_are_coh x);tauto. *)
  (* Qed. *)
  (* Lemma project_proof l x : test (is_coherent (project_list l x)) = true. *)
  (* Proof. apply test_spec,is_coherent_project_list. Qed. *)
  
  (* Definition project l (x : clique) : fcliques := *)
  (*   exist _ (project_list l x) (project_proof l x). *)

  (* Infix " @@ " := project (at level 20). *)

  (* Lemma project_spec a l x : a ∈ $ (l@@x) <-> a ⊨ x /\ a ∈ l. *)
  (* Proof. *)
  (*   unfold project,project_list,satisfies,satClique;simpl. *)
  (*   rewrite filter_In,Is_true_iff_eq_true;tauto. *)
  (* Qed. *)
  
  (* Lemma project_incl l x : $ (l @@ x) ⊆ l. *)
  (* Proof. intros a;rewrite project_spec;tauto. Qed. *)
         
  (* Lemma project_larger l x : x ⊃ ! (l @@ x). *)
  (* Proof. intro a;simpl_fc;rewrite project_spec;tauto. Qed. *)

  (* Lemma project_max l x α : $ α ⊆ l -> x ⊃ ! α -> l @@ x ⊃f α. *)
  (* Proof. *)
  (*   intros h1 h2 a h3;apply project_spec. *)
  (*   split;[apply h2;simpl_fc|apply h1];tauto. *)
  (* Qed. *)

  (* Lemma project_project l m α : *)
  (*   $(l @@ !(m @@ α)) ≈ $((l∩m) @@ α). *)
  (* Proof. *)
  (*   intros a;repeat rewrite project_spec||rewrite fc_to_clique_spec. *)
  (*   rewrite intersect_spec;tauto. *)
  (* Qed. *)

  (* Global Instance project_proper : *)
  (*   Proper (@equivalent _ ==> sequiv ==> eq_fcliques) project. *)
  (* Proof. *)
  (*   intros l1 l2 el α1 α2 eα a. *)
  (*   repeat rewrite project_spec||rewrite fc_to_clique_spec. *)
  (*   rewrite el,(eα a);reflexivity. *)
  (* Qed. *)

  (* Global Instance project_proper_inf : *)
  (*   Proper (Basics.flip(@incl _) ==> inf_cliques ==> inf_fcliques) project. *)
  (* Proof. *)
  (*   intros l1 l2 el α1 α2 eα a. *)
  (*   repeat rewrite project_spec||rewrite fc_to_clique_spec. *)
  (*   intros(h1&h2);split;[apply eα|apply el];assumption. *)
  (* Qed. *)
  
  (** Singleton cliques *)

  Lemma singleton_is_coherent a : is_coherent [a].
  Proof.
    intros x y [<-|F] [<-|F'];simpl in *;
      reflexivity||tauto.
  Qed.
  
  Remark sglf_proof a : test (is_coherent [a] /\ [a]<>[]) = true.
  Proof.
    apply test_spec;split;[apply singleton_is_coherent|discriminate].
  Qed.
  
  Definition sgl__f a : fcliques := (exist _ [a] (sglf_proof a)).

  Notation sgl := (fun a : vertex => !(sgl__f a) : clique).

  Lemma sgl_spec a b : a ⊨ (sgl b) <-> a = b.
  Proof. simpl;rewrite fc_to_clique_spec;simpl;intuition now subst. Qed.
  
End finite_cliques.
Arguments fcliques_coherent : clear implicits.
Arguments fcliques_coherent {G} {decG}.
Ltac simpl_fc := repeat rewrite fc_to_clique_spec in *.
Notation " ! " := fc_to_clique.
(* Infix " @@ " := project (at level 20). *)
Infix " ↯↯ " := fincompatible (at level 50).
Notation sgl := (fun a : vertex => !(sgl__f a) : clique).
Notation inf_fcliques := (fun a b : fcliques => $ b ⊆ $ a).
Infix " ⊃f " := inf_fcliques (at level 20).
