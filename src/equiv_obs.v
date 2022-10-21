Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations decidable_prop list_dec.
Require Export syntax_obs.

Create HintDb equiv_obs.

(** * Axiomatic equivalence of observations *)
Section s.
  Context {G : Graph}.
  Notation O := observation.
  Reserved Notation " Ax ⊢ e ≡ f " (at level 80).

  (** Smallest congruence on [observation] containing the relation [A]. *)
  Inductive equiv_Obs A : relation observation :=
  | eo_re a : A ⊢ a ≡ a
  | eo_sym a b : A ⊢ a ≡ b -> A ⊢ b ≡ a
  | eo_trans a b c : A ⊢ a ≡ b -> A ⊢ b ≡ c -> A ⊢ a ≡ c
  | eo_or a b c d : A ⊢ a ≡ c -> A ⊢ b ≡ d -> A ⊢ a ⟇ b ≡ c ⟇ d
  | eo_and a b c d : A ⊢ a ≡ c -> A ⊢ b ≡ d -> A ⊢ a ⟑ b ≡ c ⟑ d
  | eo_impl a b c d : A ⊢ a ≡ c -> A ⊢ b ≡ d -> A ⊢ a → b ≡ c → d
  | eo_ax a b : A a b -> A ⊢ a ≡ b
  where " Ax ⊢ e ≡ f " := (equiv_Obs Ax e f).
  Hint Constructors equiv_Obs : core.

  Definition inf_obs A : relation observation :=
    fun a b => A ⊢ a ⟇ b ≡ b.
  Notation " A ⊢ e ≦ f " := (inf_obs A e f) (at level 80).

  Global Instance equiv_obs_equiv A : Equivalence (equiv_Obs A).
  Proof.
    split.
    - intro;auto.
    - intros a b e;auto.
    - intros a b c e1 e2 ;eauto.
  Qed.

  Add Parametric Relation A : observation (equiv_Obs A)
      reflexivity proved by Equivalence_Reflexive
      symmetry proved by Equivalence_Symmetric
      transitivity proved by Equivalence_Transitive as eq_obs.

  
  Global Instance o_and_equiv A :
    Proper (equiv_Obs A ==> equiv_Obs A ==> equiv_Obs A) o_and.
  Proof. intros a b e1 c d e2;auto. Qed.

  Global Instance o_or_equiv A :
    Proper (equiv_Obs A ==> equiv_Obs A ==> equiv_Obs A) o_or.
  Proof. intros a b e1 c d e2;auto. Qed.
  
  Global Instance o_impl_equiv A :
    Proper (equiv_Obs A ==> equiv_Obs A ==> equiv_Obs A) o_impl.
  Proof. intros a b e1 c d e2;auto. Qed.
  
  Global Instance Ax_impl_eq A : subrelation A (equiv_Obs A)
    := (@eo_ax A).

  (** Union of relations, useful to build axiomatisations *)
  Inductive join (A B : relation O) : relation O :=
  | jleft s t : A s t -> join A B s t
  | jright s t : B s t -> join A B s t.
  Infix " (+) " := join (at level 20).
  
  Global Instance join_proper_left A B :
    subrelation A (equiv_Obs (A(+)B))
    := fun s t p => (eo_ax (jleft B p)).
  Global Instance join_proper_right A B :
    subrelation B (equiv_Obs (A(+)B))
    := fun s t p => (eo_ax (jright A p)).

  Reserved Notation " e =ha f " (at level 80).
  Reserved Notation " x =obs y " (at level 80).
  Reserved Notation " x =obs' y " (at level 80).

  (** Axioms of Heyting algebras *)
  Inductive ha_ax : relation observation :=
  | ha_and_ass a b c : a ⟑ (b ⟑ c) =ha (a ⟑ b) ⟑ c
  | ha_and_comm a b : a ⟑ b =ha b ⟑ a
  | ha_and_top a : a ⟑ ⊤o =ha a
  | ha_or_ass a b c : a ⟇ (b ⟇ c) =ha (a ⟇ b) ⟇ c
  | ha_or_comm a b : a ⟇ b =ha b ⟇ a
  | ha_or_bot a : a ⟇ ⊥o =ha a
  | ha_abs1 a b : a ⟇ (a ⟑ b) =ha a
  | ha_abs2 a b : a ⟑ (a ⟇ b) =ha a
  | ha_tauto a : a → a =ha ⊤o
  | ha_impl_premise a b : a ⟑ (a→b) =ha a ⟑ b
  | ha_impl_concl a b : b ⟑ (a→b) =ha b
  | ha_impl_distr a b c :  a → (b ⟑ c) =ha (a→b) ⟑ (a→c)
  where " e =ha f " := (ha_ax e f).

  (** Extra axiom of observation lattices *)
  Inductive obs_ax : relation observation :=
  | obs_incoh a b: a ⌣ b -> ⦑a⦒ ⟑ ⦑b⦒ =obs ⊥o
  where " x =obs y " := (obs_ax x y).

  Context {decG : DecidableGraph G}.

  (** Axioms valid on decidable graphs *)
  Inductive obs'_ax : relation observation :=
  | obs_clique_impl α s t :
      (π α → (s ⟇ t)) =obs' (π α → s) ⟇ (π α → t)
  | obs_clique_obs α a :
      ~a ∈ $α -> (π α → ⦑a⦒) =obs' (π α → ⊥o) ⟇ ⦑a⦒
  where " x =obs' y " := (obs'_ax x y).
End s.

Notation " Ax ⊢ e ≡ f " := (equiv_Obs Ax e f) (at level 80).
Notation " A ⊢ e ≦ f " := (inf_obs A e f) (at level 80).

Infix " (+) " := join (at level 20).
Infix " =ha " := ha_ax (at level 80).
Infix " =obs " := obs_ax (at level 80).
Infix " =obs' " := obs'_ax (at level 80).
Notation Obs := (ha_ax (+) obs_ax).
Notation Obs' := (ha_ax (+) (obs_ax(+)obs'_ax)).
#[global] Hint Constructors equiv_Obs ha_ax obs_ax obs'_ax join : equiv_obs.
