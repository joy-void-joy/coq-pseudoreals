From mathcomp Require Import ssreflect ssrnat fintype ssrbool ssrfun eqtype finfun seq.
Load reflect_rewrite.

Section List_complement.
(* Since we work on non-decidable types, we will mainly use List.In *)
Lemma inP {A: eqType} x (s: seq A): reflect (List.In x s) (x \in s).
elim: s => [|a l /= Hrec]; first by constructor.
rewrite in_cons eq_sym.
  by apply/orTP/predU1P.
Qed.

Fixpoint any_rec {A: Type } (P: A -> Prop) (s: seq A) := if s is x::s' then P x \/ any_rec P s' else False.
Definition any {A: Type} := nosimpl (any_rec (A:=A)).
End List_complement.

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

Definition seqpos_unsplit {A: Type} {s s': seq A}: ('J_s + 'J_s') -> 'J_(s++s').
Proof. by move => /unsplit/(cast_ord (sym_eq (size_cat _ _))). Defined.

(* Useful lemma to assert that a list is not empty, based on a correct position of it *)
Inductive uncons_spec {A: Type} (s: seq A) (i: 'J_s): forall x (s': seq A), 'J_(x::s') -> Type :=
|uncons_spec_intro x s' (i': 'J_(x::s')) of
  (forall P, P (x::s') i' -> P s i) & s = (x::s'): uncons_spec s i x s' i'.

Lemma unconsP {A: Type} (s: seq A) i: uncons_spec s i (head_safe s i) (behead s) (seqpos_uncons s i).
Proof. case: s i => [[]|]//. Qed.

Definition seq_pos0 {A: Type} (x: A) (s: seq A): 'J_(x::s).
Proof. by move => /=; eexists ord0. Defined.

Definition seq_cons {A: Type} (x: A) (s: seq A): 'J_s -> 'J_(x::s).
Proof. move => -[n le]; by eexists n.+1; apply/le. Defined.

(* Another useful induction lemma. This one allows us to do an induction on both a sequence and a position of the sequence *)
Lemma size_ind {A} s i (P: forall (s: seq A) (i: 'J_s), Type) : (forall x (s': seq A), P (x::s') (seq_pos0 x s')) -> (forall x s' j, P s' j -> P (x::s') (seq_cons x s' j)) -> P s i.
Proof.
move => HInit Hrec.
elim: s i => [|x s IHs [n le]]; first by case.
case: n le => [le|n le {HInit}];
  first by rewrite (bool_irrelevance le (ltn_ord ord0)); apply: HInit.
have ln: n < size s by done.
pose a := Ordinal ln.
by move: (IHs a) => /(Hrec x) /=; rewrite (bool_irrelevance le ln).
Qed.

Lemma head_correct {A: Type} (s: seq A) x i : head_safe s i = head x s.
Proof. by case: (unconsP s i) => x' s' _ _ ->. Qed.

Fixpoint nth_safe {A: Type} (s: seq A) (n: 'J_s): A.
Proof.
move: n => -[n p]; case: n s p => [|n]; (case; [done | idtac]).
- exact.
- move => x s le; apply: (nth_safe _ s); by exists n.
Defined.

Lemma nth_safe_is_nth {A: Type} (d: A) (s: seq A) (n: 'J_s): nth_safe s n = nth d s n.
Proof. elim/(size_ind s): n => {s}; by move => // x s -[] Hrec /=. Qed.

Lemma nth_safeQ {A: Type} (s: seq A) (x: A): List.In x s <-> exists i, nth_safe s i = x.
Proof.
split.
- elim: s => // a s IHs.
  case => [->|/IHs-[[n le] eqnx]]; first by exists ord0.
  by unshelve eexists (Ordinal (m:=n.+1) _).

- by move => []; elim/(size_ind s) => {s} [x' s | x' s [n le] /= Hrec /Hrec]; [left | right].
Qed.

Lemma nth_safeP {A: eqType} (s: seq A) (x: A): reflect (exists i, nth_safe s i = x) (x \in s).
  apply/equivP; last exact/nth_safeQ.
  exact/inP.
 Qed.

Variant seqpos_split_spec {A: Type} {s s': seq A} (i: 'J_(s ++ s')) : 'J_s + 'J_s' -> bool -> Type :=
  | SeqposSplitLo (j : 'J_s)  of nth_safe (s++s') i = nth_safe s  j     : seqpos_split_spec i (inl _ j) true
  | SeqposSplitHi (k : 'J_s') of nth_safe (s++s') i = nth_safe s' k     : seqpos_split_spec i (inr _ k) false.

Lemma seqpos_splitP {A: Type} {s s': seq A} (i : 'J_(s ++ s')) : seqpos_split_spec i (seqpos_split i) (i < size s).
Proof.
  have x: A by move: s s' i; do 2!case => [|?]; do 1?case.
  set lt_i_m := i < (size s); rewrite /seqpos_split/split.
  case: {-}_ lt_i_m / ltnP => jk; constructor; rewrite !(nth_safe_is_nth x) nth_cat;
      by [rewrite jk|rewrite ltnNge jk].
Qed.

Definition filter_ord {A: Type} p (s: seq A) (i: 'J_(filter p s)): 'J_s.
Proof.
  elim: s i => [[] //|x s IHs].
  case/boolP: (p x) => /= [-> | /negbTE -> /IHs/(seq_cons x) //].
  rewrite -cat1s => i.
  case/seqpos_split: {-}(i) => [_|];
  [by move => /=; eexists (ord0)|by (move => /IHs/(seq_cons x))].
Defined.
