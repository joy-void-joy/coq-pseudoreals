From mathcomp Require Import ssreflect ssrnat fintype ssrbool ssrfun eqtype finfun seq.
Load reflect_rewrite.

(* Since we work on non-decidable types, we will mainly use List.In *)
Lemma inP {A: eqType} x (s: seq A): reflect (List.In x s) (x \in s).
elim: s => [|a l /= Hrec]; first by constructor.
rewrite in_cons eq_sym.
by apply/orTP/predU1P.
Qed.

Section SeqPos.
(* This section focus on correctly assessed positions of a list. *)
Definition seqpos {A: Type} (s: seq A) := 'I_(size s).
Notation "''J_' s" := (seqpos s) (at level 8, s at level 2, format "''J_' s").

Definition head_safe {A: Type} (s: seq A) (i: 'J_s): A.
Proof. by case: s i => [[]|]//. Defined.

Definition seqpos_uncons {A: Type} (s: seq A) (i: 'J_s): 'J_((head_safe s i)::(behead s)).
Proof. by case: s i => [[]|]//. Defined.

Definition seqpos_split {A: Type} {s s': seq A}: 'J_(s ++ s') -> 'J_s + 'J_s'.
Proof. by move => /(cast_ord (size_cat _ _))/split. Defined.

(* Useful lemma to assert that a list is not empty, based on a correct position of it *)
Inductive uncons_spec {A: Type} (s: seq A) (i: 'J_s): forall x (s': seq A), 'J_(x::s') -> Type :=
|uncons_spec_intro x s' (i': 'J_(x::s')) of 
  (forall P, P (x::s') i' -> P s i) & s = (x::s'): uncons_spec s i x s' i'.

Lemma unconsP {A: Type} (s: seq A) i: uncons_spec s i (head_safe s i) (behead s) (seqpos_uncons s i).
Proof. case: s i => [[]|]//. Qed.

Definition seq_pos0 {A: Type} (x: A) (s: seq A): 'J_(x::s).
Proof. by move => /=; eexists ord0. Defined.

Lemma seq_cons {A: Type} (x: A) (s: seq A): 'J_s -> 'J_(x::s).
move => -[n le].
eexists n.+1; apply/le.
Defined.

(* Another useful induction lemma. This one allows us to do an induction on both a sequence and a position of the sequence *)
Lemma size_ind {A} s i (P: forall (s: seq A) (i: 'J_s), Type) : (forall x (s': seq A), P (x::s') (seq_pos0 x s')) -> (forall x s' j, P s' j -> P (x::s') (seq_cons x s' j)) -> P s i.
Proof.
move => HInit Hrec.
elim: s i => [|x s IHs [n le]]; first by case.
case: n le => [le|n le {HInit}];
  first by rewrite (bool_irrelevance le (ltn_ord ord0)); apply: HInit.
have ln: n < size s by done.
pose a := Ordinal ln.
move: (IHs a) => /(Hrec x) /=; by rewrite (bool_irrelevance le ln).
Qed.

Lemma head_correct {A: Type} (s: seq A) x i : head_safe s i = head x s.
Proof. by case: (unconsP s i) => x' s' _ _ ->. Qed.

Fixpoint nth_safe {A: Type} (s: seq A) (n: 'J_s): A.
Proof.
move: n => -[n p]; case: n s p => [|n]; (case; [done | idtac]).
- exact.
- move => x s le; apply: (nth_safe _ s); by exists n.
Defined.

Lemma nth_safe_is_nth {A: Type} (d: A) (s: seq A) (n: 'J_s): nth d s n = nth_safe s n.
Proof. elim/(size_ind s): n => {s}; by move => // x s -[] Hrec /=. Qed.

Lemma nth_safeQ {A: Type} (s: seq A) (x: A): List.In x s <-> exists i, nth_safe s i = x.
Proof.
split.
- elim: s => // a s IHs.
  case => [->|/IHs-[[n le] eqnx]]; first by exists ord0.
  by unshelve eexists (Ordinal (m:=n.+1) _).

- move => []; elim/(size_ind s) => {s} x' s; first by left.
  by move => -[n le] /= Hrec /Hrec; right.
Qed.