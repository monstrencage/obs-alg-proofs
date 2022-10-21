Require Export Eqdep Setoid Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation " $ o " := (proj1_sig o) (at level 0).
Infix " ∘ " := Basics.compose (at level 40).
Infix " ⊕ " := Nat.max (at level 40).

Create HintDb simpl_typeclasses.
Ltac rsimpl := repeat autorewrite with simpl_typeclasses||simpl.
Tactic Notation "rsimpl" "in" hyp(h) :=
  (repeat autorewrite with simpl_typeclasses in h||simpl in h).
Tactic Notation "rsimpl" "in" "*" :=
  (repeat autorewrite with simpl_typeclasses in * ||simpl in * ).

(** Typeclass and notation for size functions. *)
Class Size (A : Type) := size : A -> nat.
Notation " ⎢ x ⎥ " := (size x).

(** A partial order is a subrelation of its equivalence relation.  *)
Global Instance PartialOrder_subrelation {X e o} `{PartialOrder X e o} :
  subrelation e o.
Proof. intros x y E;apply H;symmetry;assumption. Qed.


(** Typeclass and notation for satisfaction relations. *)
Class Satisfaction (A B : Type) := satisfies : A -> B -> Prop.
Infix " ⊨ " := satisfies (at level 10).

Section SemEquiv.
  Context {A B : Type}.
  Context {sat : Satisfaction B A}.

  (** Semantic equivalence derived from satisfaction relation. *)
  Definition sequiv: relation A :=
    (fun a b : A => forall c : B, c ⊨ a <-> c ⊨ b).
  Notation " e ≃ f " := (sequiv e f) (at level 80).

  Global Instance sequiv_Equiv : Equivalence sequiv.
  Proof.
    split.
    - intros a b;reflexivity.
    - intros a a' e b;rewrite (e b);reflexivity.
    - intros a1 a2 a3 e1 e2 b;rewrite (e1 b),(e2 b);reflexivity.
  Qed.

  (** Semantic order relation derived from satisfaction relation. *)
  Definition ssmaller : relation A :=
    (fun a b => forall c, c ⊨ a -> c ⊨ b).
  Notation " e ≲ f " := (ssmaller e f) (at level 80).

  Global Instance ssmaller_PreOrder : PreOrder ssmaller.
  Proof.
    split.
    - intros a b h;apply h.
    - intros a1 a2 a3 e1 e2 b h;apply e2,e1,h. 
  Qed.

  Global Instance ssmaller_PartialOrder : PartialOrder sequiv ssmaller.
  Proof.
    intros a a';split;unfold Basics.flip;simpl.
    - intros e;split;intros b h;apply e,h.
    - intros (h1&h2) b;split;[apply h1|apply h2].
  Qed.


  Global Instance satisfies_proper b :
    Proper (sequiv ==> iff) (satisfies b).
  Proof. intros x y E;apply E. Qed.

  Global Instance satisfies_inf b :
    Proper (ssmaller ==> Basics.impl) (satisfies b).
  Proof. intros x y E h;apply (E b),h. Qed.
End SemEquiv.
Notation " e ≲ f " := (ssmaller e f) (at level 80).

Notation " e ≃ f " := (sequiv e f) (at level 80).
