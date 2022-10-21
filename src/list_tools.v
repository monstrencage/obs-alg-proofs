(** * RIS.list tools : Toolbox of list operators and their properties. *)

Require Import notations Psatz Bool.
Require Export List.
Export ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Global Hint Unfold Basics.compose : core.


(** * Lists *)

(** ** Notations *)
(** We associate the traditional containment symbol to list inclusion. *)
Infix " ⊆ " := incl (at level 80).

(** We use the following symbol to denote the membership predicate. *)
Infix " ∈ " := In (at level 60).

(** We'll write [P :> l] for the list [l] where we've removed elements that do not satisfy the boolean predicate [P]. *)
Infix " :> " := filter (at level 50).

(** The size of a list is its length. *)
Global Instance SizeList {A} : Size (list A) := (@length A).

Remark SizeLength {A : Type} (l : list A) : length l = ⎢l⎥.
Proof. reflexivity. Qed.
Remark SizeCons {A:Type} (a : A) (l : list A) : ⎢a::l⎥ = S ⎢l⎥.
Proof. reflexivity. Qed.
Remark SizeNil {A:Type} : ⎢@nil A⎥ = 0.
Proof. reflexivity. Qed.
Remark SizeApp {A:Type} (l m : list A) : ⎢l++m⎥ = ⎢l⎥+⎢m⎥.
Proof. setoid_rewrite app_length;reflexivity. Qed.
Remark SizeMap {A B:Type} (l : list A) (f : A -> B): ⎢map f l⎥ = ⎢l⎥.
Proof. setoid_rewrite map_length;reflexivity. Qed.
Global Hint Rewrite @SizeLength @SizeCons @SizeNil @SizeApp @SizeMap: simpl_typeclasses.

(** ** Induction principles *)

(** Induction principle for lists in the reverse order. *)
Lemma rev_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, P l -> P (l++[a])) -> forall l, P l.
Proof.
  intros;rewrite <- rev_involutive;induction (rev l);simpl;auto.
Qed.

(** Strong induction on the length of a list. *)
Lemma len_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, (forall m, ⎢m⎥ <= ⎢l⎥ -> P m) -> P (a::l)) -> forall l, P l.
Proof.
  intros h0 hn l;remember ⎢l⎥ as N.
  assert (len:⎢l⎥ <= N) by lia.
  clear HeqN;revert l len;induction N.
  - intros [|a l];rsimpl;try lia;auto.
  - intros [|a l];rsimpl;auto.
    intro len;apply hn;intros m;simpl;intros len'.
    apply IHN;lia.
Qed.

(** Strong induction on the length of a list, taken in the reverse order. *)
Lemma len_rev_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, (forall m, ⎢m⎥ <= ⎢l⎥ -> P m) -> P (l++[a])) -> forall l, P l.
Proof.
  intros h0 hn l;remember ⎢l⎥ as N.
  assert (len:⎢l⎥ <= N) by lia.
  clear HeqN;revert l len;induction N.
  - intros [|a l];rsimpl;try lia;auto.
  - intros l0;case_eq l0;[intros->;simpl;auto|].
    intros a0 l0' _;destruct (@exists_last _ (a0::l0')) as (l&a&->);[discriminate|].
    rsimpl;intro len;apply hn;intros m;simpl;intros len'.
    apply IHN;lia.
Qed.

(** ** General lemmas *)
(** A list is not empty if and only if it has a last element. *)
Lemma not_nil_add {A} (v : list A) : v <> [] <-> exists u l, v = u++[l].
Proof.
  split.
  - induction v;try tauto.
    intros _;destruct v.
    + exists [];exists a;reflexivity.
    + destruct IHv as (u&x&->);try discriminate.
      exists (a::u),x;split.
  - intros (u&l&E) -> .
    apply app_cons_not_nil in E;auto.
Qed.

(** A list is either empty or can be decomposed with its last element apparent.*)
Lemma nil_or_last {A} (v : list A) : {v = []} + {exists a v', v = v'++[a]}.
Proof.
  induction v.
  - left;reflexivity.
  - right;destruct IHv as [->|(b&v'&->)].
    + exists a,[];reflexivity.
    + exists b,(a::v');reflexivity.
Qed.

(** If the list [l++a::l'] is duplicate free, so are [l] and [l']. *)
Lemma NoDup_remove_3 {A} (l l' : list A) (a : A) :
    NoDup (l ++ a :: l') -> NoDup l /\ NoDup l'.
Proof.
  revert l' a;induction l;intros l' b;simpl;
    repeat rewrite NoDup_cons_iff.
  - intros (_&h);split;auto;apply NoDup_nil.
  - rewrite in_app_iff;intros (N&hyp);apply IHl in hyp as (h1&h2);
      repeat split;auto.
Qed.

(** Filtering a concatenation is the same as concatenating filters. *)
Lemma filter_app {A} (f : A -> bool) (l m : list A) :
  f :> (l++m) = f :> l ++ f :> m.
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;auto.
  f_equal;auto.
Qed.

(** Filtering reduces the length of the list. *)
Lemma filter_length {A} (f : A -> bool) l :
  ⎢f :> l⎥ <= ⎢l⎥ .
Proof.
  induction l;rsimpl;auto.
  destruct (f a);rsimpl;lia.
Qed.

(** The following lemma give a more precise description. *)
Lemma filter_length_eq {A} (f : A -> bool) l :
  ⎢f :> l⎥ + ⎢(fun x => negb (f x)) :> l⎥ = ⎢l⎥ .
Proof.
  induction l;rsimpl;auto.
  destruct (f a);rsimpl;lia.
Qed.

(** If there is an element in [l] not satisfying f, then  [f :> l] is strictly smaller than [l]. *)
Lemma filter_length_lt {A} (f : A -> bool) (l : list A) a :
  a ∈ l -> f a = false -> ⎢f :> l⎥<⎢l⎥.
Proof.
  induction l as [|b L];simpl;[tauto|].
  intros [<-|I].
  - intros ->;rsimpl.
    pose proof (filter_length f L) as hyp;lia.
  - intros F;pose proof (IHL I F) as hyp.
    destruct (f b);rsimpl;lia.
Qed.

(** [filter] and [map] commute. *)
Lemma filter_map {A B} (f : A -> bool) (g : B -> A) l :
  f :> (map g l) = map g ((fun x => f (g x)) :> l).
Proof.
  induction l;simpl;auto.
  unfold Basics.compose;destruct (f (g a));simpl;auto.
  f_equal;auto.
Qed.

(** [filter] only depends on the values of the filtering function, not its implementation. *)
Lemma filter_ext_In {A} (f g : A -> bool) l :
  (forall x, x ∈ l -> f x = g x) -> f :> l = g :> l.
Proof.
  intro hyp;induction l as [|x l];simpl;auto.
  case_eq (f x);case_eq (g x).
  - intros _ _; f_equal;apply IHl;intros y I;apply hyp;now right.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|symmetry].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros _ _;apply IHl;intros y I;apply hyp;now right.
Qed.

Lemma filter_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) -> f :> l = g :> l.
Proof. intros hyp;apply filter_ext_In;intros x _;apply hyp. Qed.

(** Filtering with the predicate [true] does not modify the list. *)
Lemma filter_true {A} (l : list A) :
  (fun _ => true) :> l = l.
Proof. induction l;simpl;auto;congruence. Qed.

(** Filtering preserves the property [NoDup] (absence of duplicates). *)
Lemma filter_NoDup {A} (f : A -> bool) l :
  NoDup l -> NoDup (f :> l).
Proof.
  induction l;simpl;auto.
  destruct (f a);repeat rewrite NoDup_cons_iff;
    try rewrite filter_In;tauto.
Qed.

(** A filtered list [P :> l] is empty if and only if [P x] is [false] for every element [x∈l]. *)
Lemma filter_nil {A} (P : A -> bool) l :
  P:>l = [] <-> forall a, a ∈ l -> P a = false.
Proof.
  induction l;simpl;[tauto|].
  case_eq (P a);intro E.
  - split;[discriminate|].
    intro h;exfalso;pose proof (h a) as F;rewrite E in F.
    intuition discriminate.
  - rewrite IHl;clear IHl;firstorder subst;auto.
Qed.
  
(** If two concatenations are equal, and if the two initial factors have the same length, then the factors are equal. *)
Lemma length_app {A} (l1 l2 m1 m2 : list A) :
  ⎢l1⎥ = ⎢m1⎥ -> l1++l2 = m1++m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros El Ea.
  cut (l1 = m1).
  - intros ->;split;auto.
    eapply app_inv_head,Ea.
  - transitivity (firstn ⎢l1⎥ (l1++l2)).
    + rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r.
      setoid_rewrite firstn_all;reflexivity.
    + rewrite Ea,El.
      rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r;setoid_rewrite firstn_all;reflexivity.
Qed.

(** If two concatenations are equal, and if the two final factors have the same length, then the factors are equal. *)
Lemma length_app_tail {A} (l1 l2 m1 m2 : list A) :
  ⎢l2⎥ = ⎢m2⎥ -> l1++l2 = m1++m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros L;revert m1;induction l1;intros [|b m];rsimpl;auto.
  - intros ->;exfalso;rsimpl in L;lia.
  - intros <-;exfalso;rsimpl in L;lia.
  - intro E;inversion E as [[Ea El]];apply IHl1 in El as (->&->);auto.
Qed.

(** If two concatenations are equal, and the first initial factor is
smaller than the second one, we can find a unifying factor [w]. *)
Lemma app_eq_app_length {A : Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1 ++ v2 -> ⎢u1⎥ <= ⎢v1⎥ -> exists w, v1 = u1++w /\ u2 = w++v2.
Proof.
  set (k:= ⎢v1⎥ - ⎢u1⎥ ).
  intros E L.
  assert (EL : ⎢u1 ++ u2⎥ = ⎢v1 ++ v2⎥) by (rewrite E;reflexivity).
  repeat rewrite app_length in EL.
  rewrite <- (firstn_skipn k u2) in E.
  rewrite <- (firstn_skipn k u2).
  rewrite <-app_ass in E.
  apply length_app in E as (E1 & E2).
  - rewrite <-E1, <-E2;eexists;eauto.
  - rsimpl in *;setoid_rewrite firstn_length_le;rsimpl;unfold k;lia.
Qed.

(** If two concatenations are equal, we can always find a unifying factor. *)
Lemma Levi {A:Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1++v2 -> exists w, (u1=v1++w /\ v2=w++u2) \/ (v1=u1++w /\ u2=w++v2).
Proof.
  intro E;destruct (Compare_dec.le_lt_dec ⎢u1⎥ ⎢v1⎥ ) as [L|L].
  - apply (app_eq_app_length E) in L as (w&->&->).
    exists w;right;auto.
  - symmetry in E;apply app_eq_app_length in E as (w&->&->);[|lia].
    exists w;left;auto.
Qed.

(** This next lemma makes the unifying factor unambiguous. *)
Lemma Levi_strict {A:Set} (u1 u2 v1 v2 : list A) :
  u1++u2 = v1++v2 -> (u1 = v1 /\ u2 = v2)
                    \/ exists a w, (u1=v1++a::w /\ v2=a::w++u2) \/ (v1=u1++a::w /\ u2=a::w++v2).
Proof.
  intro E;destruct (Compare_dec.le_lt_dec ⎢u1⎥ ⎢v1⎥ ) as [L|L];
    [apply Compare_dec.le_lt_eq_dec in L as [L|L]|].
  - apply app_eq_app_length in E as (w&->&->);[|lia];rsimpl in L.
    destruct w as [|a w];[rsimpl in L;lia|].
    right;exists a,w;right;auto.
  - apply length_app in E;tauto.
  - symmetry in E;apply app_eq_app_length in E as (w&->&->);[|lia].
    rsimpl in L;destruct w as [|a w];[rsimpl in L;lia|].
    right;exists a,w;left;auto.
Qed.

Ltac levi u v :=
  let a := fresh "a" in
  let w := fresh "w" in
  let h := fresh "h" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  assert (h:u=v);
  [auto
  |destruct (Levi_strict h) as [E1|(a&w&[E1|E1])];
   destruct E1 as (E1&E2);repeat (rewrite E1 in * || rewrite E2 in * )].

Tactic Notation "levi" hyp(h) :=
  let a := fresh "a" in
  let w := fresh "w" in
  let E1 := fresh "E" in
  let E2 := fresh "E" in
  destruct (Levi_strict h) as [E1|(a&w&[E1|E1])];
  destruct E1 as (E1&E2);repeat (rewrite E1 in * || rewrite E2 in * ).

(** If the concatenation of two lists is duplication free, then so are they. *)
Lemma NoDup_app_inv {X:Set} : forall (l m : list X),
    NoDup (l++m) -> NoDup l /\ NoDup m.
Proof.
  induction l;simpl;intros m nd.
  - split;auto using NoDup_nil.
  - rewrite NoDup_cons_iff in *;rewrite in_app_iff in nd.
    firstorder.
Qed.

(** If [l] and [m] don't share any element, then if both of them don't have duplication their concatenation won't either. *)
Lemma NoDup_app {X : Set} l m:
  (forall a : X, a ∈ l -> ~ a ∈ m) -> NoDup l ->  NoDup m -> NoDup (l++m).
Proof.
  intros h1 h2 h3;revert h2 m h3 h1; induction l.
  - simpl;intros;auto.
  - intros hl m hm h; inversion hl.
    simpl;apply NoDup_cons;auto.
    + rewrite in_app_iff;firstorder.
    + apply IHl;firstorder.
Qed.

(** If the boolean predicate [forallb f l] is false, then me may extract a counter-example, that is an element in the list [l] where the predicate [f] is false. *)
Lemma forallb_false_exists {A} f (l:list A) :
  forallb f l = false <-> exists a, a ∈ l /\ f a = false.
Proof.
  induction l;simpl.
  - split;[discriminate|firstorder].
  - rewrite andb_false_iff,IHl;split.
    + intros [h|(b&I&h)].
      * exists a;auto.
      * exists b;auto.
    + intros (b&[<-|I]&h);firstorder.
Qed.

(** [l] appears in the list [concat m] exactly when there is a list [L] in [m] such that [l] appears in [L]. *)
Lemma in_concat {A : Set} l (m : list (list A)) :
  l ∈ concat m <-> exists L, L ∈ m /\ l ∈ L.
Proof.
  induction m as [|L m].
  - simpl;firstorder.
  - simpl;rewrite in_app_iff,IHm;clear;firstorder (subst;tauto).
Qed.

(** If [map f m] can be split into [l1++l2], then we may split [l] into [m1++m2] accordingly. *)
Lemma map_app_inverse {A B} (f : A -> B) m l1 l2 :
  map f m = l1 ++ l2 -> exists m1 m2, l1 = map f m1 /\ l2 = map f m2 /\ m = m1 ++ m2.
Proof.
  revert m;induction l1 as [|a l1];intros l E;simpl in *.
  - exists [],l;split;auto.
  - destruct l as [|b l];simpl in E;inversion E.
    apply IHl1 in H1 as (m1&m2&->&->&->).
    exists (b::m1),m2;repeat split;auto.
Qed.

(** [lift_prod f] is the pointwise extension of the binary operation [f] over [A] into a binary operation over [list A].  *)
Definition lift_prod {A} (f : A -> A -> A) : list A -> list A -> list A :=
  fun l m => flat_map (fun a => map (f a) m) l.

Lemma lift_prod_spec {A} f (l m : list A) :
  forall c, c ∈ lift_prod f l m <-> exists a b, a ∈ l /\ b ∈ m /\ c = f a b.
Proof. intro c; unfold lift_prod;rewrite in_flat_map;setoid_rewrite in_map_iff;firstorder. Qed.

Lemma incl_map {A B:Set} (f : A -> B) l m : l ⊆ map f m -> exists n, l = map f n /\ n ⊆ m.
Proof.
  induction l as [|a l].
  - intros _;exists [];split;[reflexivity|intro;simpl;tauto].
  - intros I.
    assert (Ia : a ∈ (a :: l)) by (now left).
    apply I,in_map_iff in Ia as (b&<-&Ib).
    destruct IHl as (n&->&I').
    + intros x Ix;apply I;now right.
    + exists (b::n);split;[reflexivity|].
      apply incl_cons;tauto.
Qed.

(** ** Lists of pairs *)
(** We introduce some notations for lists of pairs: [prj1 l] is the list obtained by applying pointwise to [l] the function [fun (x,y) => x]. *)
Notation prj1 := (map fst).
(** Similarly, [prj2 l] is the list obtained by applying pointwise to [l] the function [fun (x,y) => y]. *)
Notation prj2 := (map snd).

(** If the a projection of [l] is equal to a projection of [m], then they have the same length. *)
Lemma proj_length {A B C} (l : list (A*B)) (m:list (B*C)) : prj2 l = prj1 m -> ⎢l⎥=⎢m⎥.
Proof. intro E;setoid_rewrite<-(map_length snd);rewrite E;rsimpl;reflexivity. Qed.

(** *** Combine *)
Section combine.
  Context {A B : Set}.
  Context {l1 l3 : list A} {l2 l4: list B} {l: list (A*B)}.
  Hypothesis same_length : ⎢l1⎥ = ⎢l2⎥.
  
  (** The combine function can be described by the following recursive definition : 
      - [[]⊗l = l⊗[] = []];
      - [(a::l)⊗(b::m)=(a,b)::(l⊗m)].
      In the following, we will only use [l⊗m] when [l] and [m] have the same length.
   *)
  Infix "⊗" := combine (at level 50).

  (** The first projection of [l1 ⊗ l2] is [l1]. *)
  Lemma combine_fst : prj1 (l1 ⊗ l2) = l1.
  Proof.
    revert l2 same_length;induction l1 as [|a l0];intros [|c l2];try (rsimpl;lia). 
    - intros _;reflexivity.
    - simpl;intros L.
      rewrite IHl0;auto.
  Qed.

  (** The second projection of [l1 ⊗ l2] is [l2]. *)
  Lemma combine_snd : prj2 (l1 ⊗ l2) = l2.
  Proof.
    revert l2 same_length;induction l1 as [|a l0];intros [|b l2];try (rsimpl;lia).
    - intros _;reflexivity.
    - simpl;intros L.
      rewrite IHl0;auto.
  Qed.

  (** A combination of concatenations is the concatenation of combinations (assuming the first arguments of both concatenations have the same length). *)
  Lemma combine_app : (l1++l3) ⊗ (l2++l4) = l1 ⊗ l2 ++ l3 ⊗ l4.
  Proof.
    revert l2 l3 l4 same_length;induction l1 as [|a l0];intros [|b l2] l3 l4;try (rsimpl;lia).
    - intros _;reflexivity.
    - simpl;intros L;f_equal.
      rewrite IHl0;auto.
  Qed.

  (** Every list of pairs can be expressed as the combination of its first and second components. *)
  Lemma combine_split : l = (prj1 l) ⊗ (prj2 l).
  Proof. induction l as [|(a,b)l'];simpl;auto;f_equal;auto. Qed.

End combine.
Infix "⊗" := combine (at level 50).

(** *** Mix *)
Section mix.
  Context {A B : Set} {s1 s2 s3 s4 : list (A*B)}.
  Hypothesis same_length : ⎢s1⎥ = ⎢s2⎥.

  (** Given two lists of pairs [s1] and [s2], the mix of [s1] and [s2] is the combination of the first projection of [s1] with the second projection of [s2]. We will only use this construct when [s1] and [s2] have the same length. *)
  Definition mix (s1 s2 : list (A*B)) := (prj1 s1) ⊗ (prj2 s2).
  Infix "⋈" := mix (at level 50).
  
  Lemma mix_fst : prj1 (s1 ⋈ s2) = prj1 s1.
  Proof. intros;unfold mix;rewrite combine_fst;rsimpl;auto. Qed.

  Lemma mix_snd : prj2 (s1 ⋈ s2) = prj2 s2.
  Proof. intros;unfold mix;rewrite combine_snd;rsimpl;auto. Qed.

  Lemma mix_app : (s1++s3) ⋈ (s2++s4) = s1 ⋈ s2 ++ s3 ⋈ s4.
  Proof. intros;unfold mix;rewrite map_app,map_app,combine_app;rsimpl;auto. Qed.
End mix.
Infix "⋈" := mix (at level 50).

(** *** Flip *)
Section flip.
  Context {A B : Set} {l m : list (A*B)}.

  (** Flipping a list of pairs amounts to applying pointwise to the list the function [fun (x,y) => (y,x)], that is exchanging the order of every pair in the list. *)
  Definition flip {A B} : list (A*B) -> list (B*A) := map (fun x => (snd x,fst x)).
  Notation " l ` " := (flip l) (at level 20).
  
  (** Flip is an involution. *)
  Lemma flip_involutive : l`` = l.
  Proof.
    unfold flip;rewrite map_map;simpl.
    erewrite map_ext;[apply map_id|intros (?,?);simpl;auto].
  Qed.

  (** Flip distributes over concatenations. *)
  Lemma flip_app : (l++m)`=l`++m`.
  Proof. intros;apply map_app. Qed.

  (** Flip swaps first and second projections. *)
  Lemma flip_proj1 : prj1 (l `) = prj2 l.
  Proof. unfold flip;rewrite map_map;simpl;auto. Qed.

  Lemma flip_proj2 : prj2 (l `) = prj1 l.
  Proof. unfold flip;rewrite map_map;simpl;auto. Qed.

  (** The pair [(a,b)] is in [l] if and only if [(b,a)] is in [l`]. *)
  Lemma In_flip a b : (a,b) ∈ l ` <-> (b,a) ∈ l.
  Proof.
    unfold flip;rewrite in_map_iff;split.
    - intros ((c,d)&E&I);inversion E;subst;auto.
    - intro I;exists (b,a);simpl;auto.
  Qed.

End flip.
Notation " l ` " := (flip l) (at level 30).


(** ** Lists as finite sets *)

(** We say that two lists are equivalent if they contain the same elements. *)
Definition equivalent A l m := forall x : A , x ∈ l <-> x ∈ m.
Infix " ≈ " := equivalent (at level 80).

(** We now establish that [≈] is a congruence, and that [⊆] is a partial order.*)
Global Instance equivalent_Equivalence T : Equivalence (@equivalent T).
Proof.
  split.
  - intros l x; firstorder.
  - intros l m h x; firstorder.
  - intros l m h n h' x; firstorder.
Qed.
Global Instance incl_PreOrder T : PreOrder (@incl T).
Proof.
  split.
  - intros l x ;firstorder.
  - intros l m h n h' x;eauto.
Qed.
Global Instance incl_PartialOrder T :
  PartialOrder (@equivalent T) (@incl T).
Proof.
  intros l m;split.
  - intros h;split;intro x; firstorder.
  - intros (h1 & h2);intro x; firstorder.
Qed.

(** Concatenation preserves both relations. *)
Global Instance incl_app_Proper T :
  Proper ((@incl T) ==> (@incl T) ==> (@incl T)) (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;intuition. Qed.
Global Instance equivalent_app_Proper T :
  Proper ((@equivalent T) ==> (@equivalent T) ==> (@equivalent T))
         (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;firstorder. Qed.

(** The operation of adding an element to a list preserves both relations. *)
Global Instance incl_cons_Proper T a :
  Proper ((@incl T) ==> (@incl T)) (cons a).
Proof. intros l m h x;simpl in *;intuition. Qed.
Global Instance equivalent_cons_Proper T a :
  Proper ((@equivalent T) ==> (@equivalent T)) (cons a).
Proof. intros l m h x;simpl in *;firstorder. Qed.

(** For any function [f], the list morphism [map f] preserves both relations. *)
Global Instance map_incl_Proper {A B} (f : A -> B) :
  Proper (@incl A ==> @incl B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  intros (y&<-&J);exists y;split;auto.
Qed.
Global Instance map_equivalent_Proper {A B} (f : A -> B) :
  Proper (@equivalent A ==> @equivalent B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  split;intros (y&<-&J);exists y;split;auto;apply I,J.
Qed.

(** For any boolean predicate [f], the filtering map [filter f] preserves both relations. *)
Global Instance filter_incl_Proper {A} (f : A -> bool) :
  Proper (@incl A ==> @incl A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  intros (J&->);split;auto.
Qed.
Global Instance filter_equivalent_Proper {A} (f : A -> bool) :
  Proper (@equivalent A ==> @equivalent A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  split;intros (J&->);split;auto;apply I,J.
Qed.

(** The lemmas [In_incl_Proper] and [In_equivalent_Proper] are completely tautological, but turn out to be useful for technical reasons. *)
Global Instance In_incl_Proper {A} (x : A): Proper ((@incl A) ==> Basics.impl) (In x).
Proof. intros l m I;firstorder. Qed.
Global Instance In_equivalent_Proper {A} (x : A): Proper ((@equivalent A) ==> iff) (In x).
Proof. intros l m I;firstorder. Qed.

(** The operation of reversing a list preserves both relations. *)
Lemma rev_equivalent {A} (l : list A) : l ≈ rev l.
Proof. intro x;apply in_rev. Qed.
Global Instance incl_rev_Proper T : Proper ((@incl T) ==> (@incl T)) (@rev T).
Proof. intros l m h x;simpl in *;repeat rewrite <-in_rev;intuition. Qed.
Global Instance equivalent_rev_Proper T : Proper ((@equivalent T) ==> (@equivalent T)) (@rev T).
Proof. intros l m h x;simpl in *;repeat rewrite <-in_rev;apply h. Qed.

(** The [flat_map] function preserves both relations. *)
Global Instance incl_flat_map_Proper A B (f : A -> list B) :
  Proper ((@incl A) ==> (@incl B)) (flat_map f).
Proof. intros l m h x;simpl in *;repeat rewrite in_flat_map;firstorder. Qed.
Global Instance equivalent_flat_map_Proper A B (f : A -> list B) :
  Proper ((@equivalent A) ==> (@equivalent B)) (flat_map f).
Proof. intros l m h x;simpl in *;repeat rewrite in_flat_map;firstorder. Qed.

(** The [lift_prod f] function preserves both relations. *)
Global Instance incl_lift_prod_Proper {A:Set} (f : A -> A -> A) :
  Proper ((@incl _) ==> (@incl _) ==> (@incl _)) (lift_prod f).
Proof.
  intros l1 l2 E1 m1 m2 E2.
  transitivity (lift_prod f l1 m2).
  - clear l2 E1.
    induction l1;simpl.
    + reflexivity.
    + rewrite E2 at 1;rewrite IHl1;reflexivity.
  - clear m1 E2.
    induction l1;simpl.
    + intro;simpl;tauto.
    + rewrite IHl1 by (rewrite <- E1;apply incl_tl;reflexivity).
      clear IHl1;intro b;rewrite in_app_iff,in_map_iff;intros [(c&<-&Ic)|I];[|assumption].
      apply lift_prod_spec;exists a,c;rewrite <- E1;simpl;tauto.
Qed.
Global Instance equivalent_lift_prod_Proper {A:Set} (f : A -> A -> A) :
  Proper ((@equivalent _) ==> (@equivalent _) ==> (@equivalent _)) (lift_prod f).
Proof.
  intros l1 l2 E1 m1 m2 E2;apply incl_PartialOrder;unfold Basics.flip;simpl;split.
  - apply incl_PartialOrder in E1 as (->&_).
    apply incl_PartialOrder in E2 as (->&_).
    reflexivity.
  - apply incl_PartialOrder in E1 as (_&->).
    apply incl_PartialOrder in E2 as (_&->).
    reflexivity.
Qed.
    
(** The following simple facts about inclusion and equivalence are convenient to have in our toolbox. *)
Lemma incl_nil T (A : list T) : [] ⊆ A.
Proof. intros x;firstorder. Qed.
Lemma incl_app_or T (A B C : list T) : A ⊆ B \/ A ⊆ C -> A⊆B++C.
Proof. intros [?|?];auto using incl_appl, incl_appr. Qed.
Create HintDb eq_list.
Lemma incl_app_split {A} (l m p : list A) : l++m ⊆ p <-> l⊆ p /\ m ⊆ p.
Proof. unfold incl;setoid_rewrite in_app_iff;firstorder. Qed.
Global Hint Resolve incl_appl incl_appr incl_nil app_assoc : eq_list.
Lemma app_idem {A} (l : list A) : l ++ l ≈ l.
Proof. intro;rewrite in_app_iff;tauto. Qed.
Lemma app_comm {A} (l m : list A) : l ++ m ≈ m ++ l.
Proof. intro;repeat rewrite in_app_iff;tauto. Qed.
Lemma incl_split {A} (l m n : list A) :
  l ⊆ m ++ n -> exists l1 l2, l ≈ l1++l2 /\ l1 ⊆ m /\ l2 ⊆ n.
Proof.
  induction l as [|a l];simpl;intro I.
  - exists [],[];split;[reflexivity|split;apply incl_nil].
  - destruct IHl as (l1&l2&E&I1&I2).
    + intros x Ix;apply I;now right.
    + assert (Ia : a ∈ (m++n)) by (apply I;now left).
      apply in_app_iff in Ia as [Ia|Ia].
      * exists (a::l1),l2;split;[rewrite E;reflexivity|].
        split;[|assumption].
        intros x [<-|Ix];[assumption|].
        apply I1,Ix.
      * exists l1,(a::l2);split;[rewrite E;intro;repeat (rewrite in_app_iff;simpl);tauto|].
        split;[assumption|].
        intros x [<-|Ix];[assumption|].
        apply I2,Ix.
Qed.

(** ** More general lemmas *)
(** If a boolean predicate [f] fails to be true for every element of a list [l], then there must exists a witnessing element [y] falsifying [f]. This is an instance of a classical principle holding constructively when restricted to decidable properties over finite domains. *)
Lemma forall_existsb {A} (f : A -> bool) l :
  ~ (forall x, x ∈ l -> f x = true) -> exists y, y ∈ l /\ f y = false.
Proof.
  induction l as [|a l].
  - intro h;exfalso;apply h.
    intros x;simpl;tauto.
  - intros h;case_eq (f a).
    + intro p;destruct IHl as (y&I&E).
      * intro h';apply h;intros x [<-|I];auto.
      * exists y;split;auto.
        now right.
    + intro E;exists a;split;auto.
      now left.
Qed.

(** In [forallb f l] we may replace [f] with a function [g] outputting the same values on the elements of [l]. *)
Lemma forallb_ext_In {A} (f g : A -> bool) l : (forall a, a ∈ l -> f a = g a) -> forallb f l = forallb g l.
Proof.
  induction l;simpl;[|f_equal];auto.
  intros h;f_equal;[apply h|apply IHl];auto.
Qed.

(** In [forallb f l] we may replace [f] with a function [g] outputting the same values. *)
Lemma forallb_ext {A} (f g : A -> bool) l : (forall a, f a = g a) -> forallb f l = forallb g l.
Proof. intro h;apply forallb_ext_In;intros;apply h. Qed.

(** For every list [l] and every function [f], [l] is a fixpoint of [map f] if and only if every element of [l] is a fixpoint of [f]. *)
Lemma map_eq_id {A} (l : list A) (f : A -> A) :
  map f l = l <-> (forall x, x ∈ l -> f x = x).
Proof.
  split.
  - intros E x I.
    apply In_nth with (d:=x) in I as (n&len&<-).
    rewrite <- map_nth with (f:=f).
    rewrite E.
    apply nth_indep,len.
  - intro E;erewrite map_ext_in;[rewrite map_id;auto|].
    intros x I;apply E;auto.
Qed.

(** [fun f => map f l] is bijective, using extensional equality of functions. *)
Lemma map_bij {A B} (f g : A -> B) l : map f l = map g l -> forall a, a ∈ l -> f a = g a.
Proof.
  induction l;simpl;auto.
  - intros;tauto.
  - intros E b [I|I];inversion E;subst;auto.
Qed.

Lemma map_ext_in_iff (A B : Type) (f g : A -> B) (l : list A) :
  (forall a : A, a ∈ l -> f a = g a) <-> map f l = map g l.
Proof.
  split;[apply map_ext_in|].
  induction l;simpl;[tauto|].
  intros h b.
  inversion h as [[h1 h2]].
  intros [<-|I].
  - assumption.
  - apply IHl,I;assumption.
Qed.

Lemma map_eq_equivalent (A B : Set) (f g : A -> B) l m :
  l ≈ m -> map f m = map g m <-> map f l = map g l.
Proof.
  intros E;rewrite <- map_ext_in_iff.
  setoid_rewrite <- E.
  rewrite map_ext_in_iff;reflexivity.
Qed.

(** We may lift a decomposition of the second (respectively first) component of a list of pairs into a decomposition of the original list. *)
Lemma split_snd {A B} a (t : list (A * B)) t1 t2 :
  prj2 t = t1 ++ a :: t2 -> ~ a ∈ t1 -> exists k s1 s2, t = s1++(k,a)::s2 /\ t1 = prj2 s1 /\ t2 = prj2 s2.
Proof.
  revert t t2;induction t1;intros [|(k,b)t] t2;simpl;try discriminate.
  - intros E _;inversion E;subst.
    exists k,[],t;simpl;auto.
  - intros E0 I;inversion E0 as [[X E]];subst;clear E0.
    apply IHt1 in E as (m&s1&s2&->&->&->);[|tauto].
    exists m,((k,a0)::s1),s2;simpl;auto.
Qed.

Lemma split_fst {A B} a (t : list (A * B)) t1 t2 :
  prj1 t = t1 ++ a :: t2 -> ~ a ∈ t1 -> exists k s1 s2, t = s1++(a,k)::s2 /\ t1 = prj1 s1 /\ t2 = prj1 s2.
Proof.
  revert t t2;induction t1;intros [|(b,k) t] t2;simpl;try discriminate.
  - intros E _;inversion E;subst.
    exists k,[],t;simpl;auto.
  - intros E0 I;inversion E0 as [[X E]];subst;clear E0.
    apply IHt1 in E as (m&s1&s2&->&->&->);[|tauto].
    exists m,((a0,k)::s1),s2;simpl;auto.
Qed.

(** If [n] is smaller than the length of [u], then [u] can be split into a prefix of size [n], followed by a non-empty list. *)
Lemma split_word {A} n (u : list A) :
  n < ⎢u⎥ -> exists x u1 u2, u = u1++x::u2 /\ ⎢u1⎥ = n.
Proof.
  induction u using rev_induction;rsimpl;[lia|].
  destruct (PeanoNat.Nat.eq_dec n ⎢u⎥) as [E|N] ;subst.
  - intros _;exists a,u,[];split;auto.
  - rsimpl;intros L;destruct IHu as (x&u1&u2&->&E);[lia|].
    exists x,u1,(u2++[a]);split;auto.
    rewrite app_ass;simpl;auto.
Qed.

(** ** Subsets of a list *)
Fixpoint subsets {A : Set} (l : list A) :=
  match l with
  | [] => [[]]
  | a::l => map (cons a) (subsets l)++subsets l
  end.

Lemma subsets_In {A : Set}(l : list A) :
  forall m, m ∈ subsets l -> m ⊆ l.
Proof.
  induction l as [|a l];intros m;simpl;try rewrite in_app_iff.
  - intros [<-|F];[reflexivity|tauto].
  - rewrite in_map_iff;intros [(m'&<-&I)|I];apply IHl in I as ->.
    + reflexivity.
    + intro;simpl;tauto.
Qed.

Lemma incl_cons_disj {A : Set} (a : A) m l :
  m ⊆ a :: l -> m ⊆ l \/ exists m', m ≈ a::m' /\ m' ⊆ l.
Proof.
  induction m as [|b m];simpl.
  - intro;left;apply incl_nil.
  - intros I.
    destruct IHm as [IH|(m'&E&IH)].
    + intros x Ix;apply I;now right.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m;split;[reflexivity|assumption].
      * left;intros c [<-|Ic];[assumption|].
        apply IH,Ic.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m';split;[|assumption].
        rewrite E;clear;intro;simpl;tauto.
      * right;exists (b::m');split.
        -- rewrite E;intro;simpl;tauto.
        -- intros c [<-|Ic];[assumption|].
           apply IH,Ic.
Qed.

Lemma subsets_spec {A : Set} (l : list A) :
  forall m, m ⊆ l <-> exists m', m' ∈ subsets l /\ m ≈ m'.
Proof.
  intro m;split.
  - revert m; induction l as [|a l];intros m L.
    + exists [];split;[simpl;tauto|].
      apply incl_PartialOrder;split;[assumption|apply incl_nil].
    + simpl;destruct (incl_cons_disj L) as [h|(m'&E&h)];apply IHl in h as (m''&I&E').
      * exists m'';split;[|assumption].
        rewrite in_app_iff;tauto.
      * exists (a::m'');split.
        -- apply in_app_iff;left;apply in_map_iff;exists m'';tauto.
        -- rewrite E,E';reflexivity.
  - intros (m'&I&->);apply subsets_In,I.
Qed.

Lemma subsets_NoDup {A : Set} (k l : list A) :
  NoDup l -> k ∈ subsets l -> NoDup k.
Proof.
  revert k;induction l as [|a l];intros k;simpl.
  - intros h [<-|F];tauto.
  - rewrite NoDup_cons_iff,in_app_iff,in_map_iff.
    intros (nI&nd) [(k'&<-&Ik')|Ik].
    + apply NoDup_cons.
      * intro h;apply nI,(subsets_In Ik'),h.
      * apply IHl;tauto.
    + apply IHl;tauto.
Qed.

(** ** Pairs *)
Definition pairs {A B : Set} l r : list (A * B) :=
  fold_right (fun a acc => (map (fun b => (a,b)) r)++acc) [] l.

Lemma pairs_spec {A B : Set} l r (a : A) (b : B) : (a,b) ∈ pairs l r <-> a ∈ l /\ b ∈ r.
Proof.
  revert a b;induction l;simpl;[tauto|].
  intros a' b;rewrite in_app_iff.
  rewrite IHl;clear IHl.
  rewrite in_map_iff.
  split.
  - intros [(?&E&Ib)|I].
    + inversion E;subst;tauto.
    + tauto.
  - intros ([<-|Ia]&Ib).
    + left;exists b;tauto.
    + right;tauto.
Qed.

(** ** Enumerate lists of a certain length *)
Fixpoint lists_of_length {A} (elts:list A) n :=
  match n with
  | 0 => [[]]
  | S n => flat_map (fun l => map (fun e => e::l) elts) (lists_of_length elts n)
  end.

Lemma lists_of_length_spec {A} (elts : list A) n l :
  l ∈ lists_of_length elts n <-> ⎢l⎥ = n /\ l ⊆ elts.
Proof.
  revert l;induction n;intros l;simpl.
  - split.
    + intros [<-|F];[|tauto].
      split;[reflexivity|apply incl_nil].
    + destruct l;[tauto|simpl;intros (F&_);discriminate].
  - rewrite in_flat_map;setoid_rewrite IHn;clear IHn.
    setoid_rewrite in_map_iff.
    split.
    + intros (m&(Len&Lm)&(a&<-&Ia)).
      split;[rsimpl;rewrite Len;reflexivity|].
      apply incl_cons;tauto.
    + intros (Len&Incl).
      destruct l as [|a l];simpl in Len;inversion Len as [[Len']].
      exists l;split.
      * split;[reflexivity|].
        intros x Ix;apply Incl;now right.
      * exists a;split;[reflexivity|].
        apply Incl;now left.
Qed.

(** ** Pad a list with an element *)
Definition pad {A} (e : A) (l : list A) := e::flat_map (fun a => [a;e]) l.

Lemma pad_contents {A} (e : A) l : pad e l ≈ e::l.
Proof.
  unfold pad;induction l;simpl.
  - reflexivity.
  - rewrite IHl;intro;simpl;tauto.
Qed.

(** * Sum function *)
(** If [a1,...,an] are elements in [A] and [f] is a function from [A] to [nat], then [sum f [a1;...;an]] is the natural number [f a1+...+f an]. *)
Definition sum {A} f (l : list A) := fold_right (fun a acc => f a + acc) 0 l.

(** [sum f] distributes over concatenations. *)
Lemma sum_app {A} f (l m : list A) : sum f (l++m) = sum f l + sum f m.
Proof. induction l;simpl;try lia. Qed.

(** If [l] is contained in [m] and has no duplicates, then summing [f] on [l] yields a smaller value than summing [f] on [m]. *)
Lemma sum_incl_ND {A} f (l m : list A) :
  l ⊆ m -> NoDup l -> sum f l <= sum f m.
Proof.
  revert m;induction l;intros m Incl ND;simpl.
  - lia.
  - assert (Ia: a ∈ m) by (apply Incl;now left).
    apply in_split in Ia as (m1&m2&->).
    rewrite sum_app;simpl.
    apply NoDup_cons_iff in ND as (Ia&ND).
    apply (IHl (m1++m2)) in ND.
    + rewrite sum_app in ND;lia.
    + intro x;pose proof (Incl x) as h;revert h.
      repeat rewrite in_app_iff;simpl;intuition subst;tauto.
Qed.

(** If two duplicate-free list are equivalent, then summing [f] on any of them yields the same result. *)
Lemma sum_eq_ND {A} f (l m : list A) :
  l ≈ m -> NoDup l -> NoDup m -> sum f l = sum f m.
Proof.
  revert m;induction l;intros m Eq NDl NDm;simpl.
  - destruct m as [|a m];[simpl;lia|].
    exfalso;cut (a ∈ []);[simpl;tauto|].
    rewrite Eq;now left.
  - assert (Ia: a ∈ m) by (apply Eq;now left).
    apply in_split in Ia as (m1&m2&->).
    rewrite sum_app;simpl.
    apply NoDup_cons_iff in NDl as (Ial&NDl).
    apply NoDup_remove in NDm as (Iam&NDm).
    apply (IHl (m1++m2)) in NDl;auto.
    + rewrite sum_app in NDl;lia.
    + intro x;pose proof (Eq x) as h;revert h NDm.
      repeat rewrite in_app_iff;simpl;intuition subst;tauto.
Qed.

(** If [f] is pointwise smaller than [g], then the sum [sum f l] is smaller than [sum g l]. *)
Lemma sum_incr {A} f g (l : list A) : (forall x, f x <= g x) -> sum f l <= sum g l.
Proof.
  intro h;induction l;simpl;auto.
  pose proof (h a);lia.
Qed.

(** [sum f l] only depends on the values of [f], not its implementation. *)
Lemma sum_ext {A} f g (l : list A) : (forall x, f x = g x) -> sum f l = sum g l.
Proof. intro h;induction l;simpl;auto. Qed.

Lemma sum_ext_In {A} f g (l : list A) : (forall x, x ∈ l -> f x = g x) -> sum f l = sum g l.
Proof.
  induction l.
  - intro;reflexivity.
  - intro h;simpl.
    rewrite IHl,h;auto.
    + now left.
    + intros x I;apply h;now right.
Qed.

(** If [h] is the pointwise sum of [f] and [g], then [sum h l] is the sum of [sum f l] and [sum g l]. *)
Lemma sum_add {A} f g h (l : list A) : (forall x, h x = f x + g x) -> sum h l = sum f l + sum g l.
Proof.
  intro H;induction l;simpl;auto.
  pose proof (H a);lia.
Qed.

Lemma sum_add_distr {A} f g (l : list A) : sum f l + sum g l = sum (fun x => f x + g x) l.
Proof. symmetry;apply sum_add;tauto. Qed.

(** If [f] is uniformly [0] on the elements of the list [l], then [sum f l] is [0]. *)
Lemma sum_zero_in {A} f (l : list A) : (forall x, x ∈ l -> f x = 0) -> sum f l = 0.
Proof.
  induction l;intro hyp;simpl;auto.
  rewrite IHl,(hyp a);auto.
  - now left.
  - intros;apply hyp;now right.
Qed.

Lemma sum_le {A} f g (l : list A) :
  (forall a, a∈ l -> f a <= g a) -> sum f l <= sum g l.
Proof.
  induction l as [|a l];simpl.
  - intros _ ;reflexivity.
  - intros h;cut (f a<= g a /\ sum f l <= sum g l);[lia|split].
    + apply h;tauto.
    + apply IHl;intros b I;apply h;tauto.
Qed.

Lemma sum_lt {A} f g (l : list A) :
  (forall a, a∈ l -> f a <= g a) -> (exists b, b ∈ l /\ f b < g b) -> sum f l < sum g l.
Proof.
  induction l as [|a l];simpl.
  - intros _ (b&F&_);tauto.
  - intros h (b&[<-|Ib]&hb).
    + cut (sum f l <= sum g l);[lia|].
      apply sum_le;intros c Ic;apply h;tauto.
    + cut (f a <= g a /\ sum f l < sum g l);[lia|split].
      * apply h;tauto.
      * apply IHl.
        -- intros c Ic;apply h;tauto.
        -- exists b;split;auto.
Qed.

Lemma sum_filter {A : Set} (P : A -> bool) f l : sum f (P:>l) <= sum f l.
Proof. induction l as [|a l];simpl;[|destruct (P a)];simpl;lia. Qed.

  
(** * Enumerate permutations of a list *)
Section shuffle.
  Context {A : Set}.

  (** [insert a l] generates the list of all possibles lists [l1::a++l2] such that [l=l1++l2]. *)
  Fixpoint insert (a : A) l :=
    match l with
    | [] => [[a]]
    | b::l => (a::b::l)::(map (cons b) (insert a l))
    end.

  (** [shuffles l] generates the list of all lists obtained by reordering the elements of [l]. For instance [shuffles [a;b]=[[a;b];[b;a]]]. *)
  Fixpoint shuffles l :=
    match l with
    | [] => [[]]
    | a::l => flat_map (insert a) (shuffles l)
    end.

  Lemma insert_spec a l m :
    m ∈ insert a l <-> exists l1 l2, l = l1++l2 /\ m = l1++a::l2.
  Proof.
    revert m;induction l as [|b l];intros m;simpl.
    - split.
      + intros [<-|F];[|tauto];exists [],[];split;reflexivity.
      + intros (l1&l2&h&->);symmetry in h; apply app_eq_nil in h as (->&->).
        simpl;left;reflexivity.
    - rewrite in_map_iff;split.
      + intros [<-|(m'&<-&I)].
        * exists [],(b::l);simpl;split;reflexivity.
        * apply IHl in I as (l1&l2&->&->).
          exists (b::l1),l2;split;reflexivity.
      + intros (l1&l2&e&->).
        destruct l1 as [|c l1].
        * simpl in e;subst;simpl.
          left;reflexivity.
        * simpl in e;inversion e;subst;clear e.
          right;exists (l1++a::l2).
          split;[reflexivity|].
          apply IHl.
          exists l1,l2;tauto.
  Qed.

  (** Shuffles of [l] contain the same elements. *)
  Lemma shuffles_equiv l m : m ∈ shuffles l -> l ≈ m.
  Proof.
    revert m;induction l;intros m h;simpl in *.
    - destruct h as [<-|F];[reflexivity|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply insert_spec in Im as (m1&m2&->&->).
      apply IHl in Ix as ->;intro;simpl;repeat rewrite in_app_iff;simpl.
      tauto.
  Qed.
  
  (** If [l] has no duplicates and [m] is a shuffle of [l], then [m] has no duplicates either. *)
  Lemma shuffles_nodup l m : NoDup l -> m ∈ shuffles l -> NoDup m.
  Proof.
    revert m;induction l;intros m nd h;simpl in *.
    - destruct h as [<-|F];[apply NoDup_nil|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply NoDup_cons_iff in nd as (nI&nd).
      apply insert_spec in Im as (m1&m2&->&->).
      rewrite (shuffles_equiv Ix) in nI;apply (IHl _ nd) in Ix.
      clear IHl l nd;induction m1;simpl.
      + apply NoDup_cons;tauto.
      + simpl in Ix;apply NoDup_cons_iff in Ix as (Ix&nd).
        apply NoDup_cons.
        * clear IHm1 nd;simpl in *;rewrite in_app_iff in *;simpl.
          firstorder (subst;tauto).
        * apply IHm1;[|assumption].
          clear IHm1 nd;simpl in *;rewrite in_app_iff in *.
          firstorder (subst;tauto).
  Qed.
  
  (** Shuffles of [l] have the same length as [l]. *)
  Lemma shuffles_length l m : m ∈ shuffles l -> ⎢l⎥ = ⎢m⎥.
  Proof.
    revert m;induction l;intros m h;rsimpl in *.
    - destruct h as [<-|F];[reflexivity|exfalso;apply F].
    - apply in_flat_map in h as (x&Ix&Im).
      apply insert_spec in Im as (m1&m2&->&->).
      apply IHl in Ix;rewrite Ix;rsimpl;lia.
  Qed.

  (** If [l] has no duplicates, then [shuffles l] contain exactly the lists that are equivalent to [l] without having any duplicates. *)
  Lemma In_shuffles l m :
    NoDup l -> m ∈ shuffles l <-> l ≈ m /\ NoDup m.
  Proof.
    intros ndl;split;[intro Il;split;[apply shuffles_equiv|apply (shuffles_nodup ndl)];apply Il|].
    revert m;induction l;intros m (e&ndm);simpl.
    - destruct m as [|a m];[tauto|].
      cut (a ∈ []);[intro F;right;apply F|].
      apply e;now left.
    - apply NoDup_cons_iff in ndl as (nI&ndl).
      assert (Em : a ∈ m) by (apply e;now left).
      apply in_split in Em as (m1&m2&->).
      apply in_flat_map;exists (m1++m2);split.
      + pose proof (NoDup_remove_2 _ _ _ ndm) as Ia.
        apply NoDup_remove_1 in ndm.
        apply IHl;[assumption|split;[|assumption]].
        clear IHl ndl ndm.
        intro b;split;simpl in *;rewrite in_app_iff in *;intro h.
        -- cut (b ∈ (a::l));[|now right].
           rewrite e,in_app_iff;simpl;clear e;firstorder (subst;tauto).
        -- cut (b ∈ (m1++a::m2)).
           ++ rewrite <-e;clear e;simpl.
              firstorder (subst;tauto).
           ++ rewrite in_app_iff;simpl;tauto.
      + apply insert_spec;exists m1,m2;tauto.
  Qed.

  (** If [l1] is a shuffle of [l2], then being a shuffle of [l1] is equivalent to being a shuffle of [l2]. *)
  Lemma eq_shuffles l1 l2 : l1 ∈ shuffles l2 -> shuffles l1 ≈ shuffles l2.
  Proof.
    revert l1;induction l2;simpl;intros l1.
    - intros [<-|F];[reflexivity|tauto].
    - rewrite in_flat_map;intros (m&Im&Il1).
      apply insert_spec in Il1 as (m1&m2&->&->).
      apply IHl2 in Im;clear IHl2.
      rewrite <- Im;clear Im l2.
      unfold equivalent;setoid_rewrite in_flat_map;
        setoid_rewrite insert_spec.
      intro x.
      transitivity (exists l1 l2, (l1 ++ l2) ∈ shuffles (m1++m2)
                             /\ x = l1++a::l2);
        [|firstorder (subst;tauto)].
      revert x;induction m1 as [|b m1];simpl.
      + intro x;rewrite in_flat_map;setoid_rewrite insert_spec.
        firstorder (subst;tauto).
      + setoid_rewrite in_flat_map; setoid_rewrite insert_spec.
        setoid_rewrite IHm1;clear IHm1.
        intro x;split;[intros (?&(x1&x2&I& -> )&(y1&y2&E& -> ) )
                      |intros (x1&x2&( ? &I&y1&y2&->&E)& -> ) ];
        levi E;subst;clear E.
        * exists (y1++[b]),x2;split;[|rewrite app_ass;reflexivity].
          eexists;split;[eassumption|].
          exists y1,x2;rewrite app_ass;split;reflexivity.
        * exists (y1++b::a0::w),x2;split;[|rewrite app_ass;reflexivity].
          eexists;split;[eassumption|].
          exists y1,(a0::w++x2);repeat rewrite app_ass;tauto.
        * symmetry in E1;inversion E1;subst;clear E1.
          exists x1,(w++b::y2);split;[|rewrite app_ass;reflexivity].
          eexists;split;[eassumption|].
          exists (x1++w),y2;repeat rewrite app_ass;tauto.
        * exists (y1++a::y2);split.
          -- exists y1,y2;tauto.
          -- exists (y1++[a]),y2;split;rewrite app_ass;reflexivity.
        * symmetry in E1;inversion E1;subst;clear E1.
          exists (y1++w++a::x2);split.
          -- exists (y1++w),x2;split;rewrite app_ass;tauto.
          -- exists y1,(w++a::x2);rewrite app_ass;tauto.
        * exists (x1 ++ a :: a0 :: w ++ y2);split.
          -- exists x1,(a0::w++y2);rewrite app_ass in I;tauto.
          -- exists (x1++a::a0::w),y2;repeat rewrite app_ass;simpl;tauto.
  Qed.
  
  (** If [l] has no duplicates, neither does [shuffles l]. *)
  Lemma NoDup_shuffles (l : list A) : NoDup l -> NoDup (shuffles l).
  Proof.
    induction l as [|a l].
    - simpl;intro;apply NoDup_cons;simpl;auto using NoDup_nil.
    - simpl;rewrite NoDup_cons_iff.
      intros (I&nd);pose proof (IHl nd) as IH;clear IHl.
      assert (e: forall m, m ∈ shuffles l -> l ≈ m /\ NoDup m).
      + intros m Im;split.
        * apply shuffles_equiv,Im.
        * apply (shuffles_nodup nd Im).
      + induction (shuffles l) as [|m L];simpl;[apply NoDup_nil|].
        assert (h:m∈(m::L)) by (now left).
        apply e in h as (eq&nd').
        apply NoDup_app.
        * intros m' Im';rewrite in_flat_map.
          intros (m''&IL&Im'').
          apply NoDup_cons_iff in IH as (Im&IH).
          rewrite insert_spec in Im',Im''.
          destruct Im' as (l1&l2&->&->).
          destruct Im'' as (m1&m2&->&E).
          levi E;inversion E1;subst;clear E E1.
          -- tauto.
          -- apply I;rewrite eq.
             rewrite app_ass,in_app_iff;simpl;tauto.
          -- apply I;rewrite eq.
             rewrite <- app_ass,in_app_iff;simpl;tauto.
        * revert nd' I;rewrite eq;clear.
          induction m as [|b m];simpl.
          -- intros;apply NoDup_cons;simpl;auto using NoDup_nil.
          -- rewrite NoDup_cons_iff.
             intros (Ib&nd) e;apply NoDup_cons.
             ++ rewrite in_map_iff;intros (l'&E&I).
                inversion E;subst.
                tauto.
             ++ assert (~ a ∈ m) as Ia by tauto.
                pose proof (IHm nd Ia) as ih;clear IHm.
                clear e Ia nd Ib.
                generalize dependent (insert a m);clear a m.
                intro l;induction l as [|a l];simpl;auto.
                repeat rewrite NoDup_cons_iff.
                rewrite in_map_iff;firstorder subst.
                intros (x&E&I);inversion E; subst;tauto.
        * apply IHL.
          -- apply NoDup_cons_iff in IH;tauto.
          -- intros m' Im';apply e;now right.
  Qed.

End shuffle.

Lemma incl_cons_disj' {A : Set} (a : A) m l :
  NoDup m -> m ⊆ a :: l -> m ⊆ l \/ exists m', m ≈ a::m' /\ m' ⊆ l /\ NoDup m'.
Proof.
  induction m as [|b m];simpl.
  - intro;left;apply incl_nil.
  - intros ND I.
    apply NoDup_cons_iff in ND as (nI&ND).
    destruct (IHm ND) as [IH|(m'&E&IH&ND')].
    + intros x Ix;apply I;now right.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m;split;[reflexivity|split;assumption].
      * left;intros c [<-|Ic];[assumption|].
        apply IH,Ic.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m';split;[|split;assumption].
        rewrite E;clear;intro;simpl;tauto.
      * right;exists (b::m');split;[|split].
        -- rewrite E;intro;simpl;tauto.
        -- intros c [<-|Ic];[assumption|].
           apply IH,Ic.
        -- apply NoDup_cons;[|assumption].
           intro F;apply nI,E;now right.
Qed.

Lemma all_subsets_nodup {A : Set} (l : list A) :
  NoDup l -> forall m, m ∈ (flat_map shuffles (subsets l)) <-> NoDup m /\ m ⊆ l.
Proof.
  intros N m;rewrite in_flat_map;split.
  - intros (k&Ik&Im).
    apply In_shuffles in Im as (E&nd).
    + split;[tauto|].
      rewrite <- E;apply subsets_In,Ik.
    + eapply subsets_NoDup;eauto.
  - intros (Nd&Incl).
    apply subsets_spec in Incl as (m'&Im'&E).
    exists m';split;[assumption|].
    apply In_shuffles.
    + apply (subsets_NoDup N);assumption.
    + rewrite <- E;split;[reflexivity|assumption].
Qed.


(* begin hide *)
Create HintDb length.
Global Hint Resolve filter_length app_length : length.

Global Instance le_plus_Proper : Proper (le ==> le ==> le) plus.
Proof. intros ? ? ? ? ? ?;lia. Qed.
Global Instance lt_plus_Proper : Proper (lt ==> lt ==> lt) plus.
Proof. intros ? ? ? ? ? ?;lia. Qed.



(*  LocalWords:  bimap
 *)
