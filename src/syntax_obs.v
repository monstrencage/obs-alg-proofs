Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import notations List.
Require Export coherence_graph_ne.

(** * Syntax for observations *)
Inductive observation {G : Graph} :=
| o_true : observation
| o_false : observation
| o_obs : vertex -> observation
| o_or : observation -> observation -> observation
| o_and : observation -> observation -> observation
| o_impl : observation -> observation -> observation.

Notation "⊤o" := o_true.
Notation "⊥o" := o_false.
Notation " ⦑ o ⦒ " := (o_obs o).
Infix " ⟇ " := o_or (at level 50).
Infix " ⟑ " := o_and (at level 50).
Infix " → " := o_impl (at level 50).

Definition Join {G : Graph} : list observation -> observation :=
  fold_right o_or ⊥o.
Definition Meet {G : Graph} : list observation -> observation :=
  fold_right o_and ⊤o.

Notation " ⋁ " := Join.
Notation " ⋀ " := Meet.

Definition π {G : Graph} {decG : DecidableGraph G} (s : fcliques) :=
  ⋀ (map o_obs ($ s)).

