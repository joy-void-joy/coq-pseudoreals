From mathcomp Require Import ssreflect ssrnat fintype ssrbool ssrfun eqtype finfun seq.
From Pseudoreals Require Import reflect_rewrite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section List_complement.
(* Since we work on non-decidable types, we will mainly use List.In *)
Lemma inP (A: eqType) x (s: seq A): reflect (List.In x s) (x \in s).
elim: s => [|a l /= Hrec]; first by constructor.
rewrite in_cons eq_sym.
by apply/orT/predU1P.
Qed.

Definition all (A: Type) (P: A -> Prop) := foldr (and \o P) True.
Definition any (A: Type) (P: A -> Prop) := foldr (or \o P) False.

Lemma revP (A: eqType) (s1 s2: seq A): (s1 == s2) = (rev s1 == rev s2).
Proof.
  case/boolP: (size s1 == size s2) => [/eqP|/eqP-s1s2].
  - move: s1 s2; apply: seq_ind2 => // x1 x2 s1 s2 _ eq.
    by rewrite eqseq_cons !rev_cons eqseq_rcons andbC eq.

  - have/eqP/negbTE-> : s1 <> s2 by move => same; apply: s1s2; rewrite same.
    by have/eqP/negbTE-> : rev s1 <> rev s2 by move => same; apply: s1s2; rewrite -size_rev -(size_rev s2) same.
Qed.
End List_complement.


Section SeqPos.
(* This section focus on correctly assessed positions of a list. *)
Definition seqpos (A: Type) (s: seq A) := 'I_(size s).
Notation "''J_' s" := (seqpos s) (at level 8, s at level 2, format "''J_' s").
 Variables (A: Type).

Definition head_safe (s: seq A) (i: 'J_s): A.
Proof. by case: s i => [[]|]//. Defined.
Lemma head_safe_correct (s: seq A) x (i: 'J_s) : head_safe i = head x s.
Proof. case: s i => //-[]//. Qed.

Definition seqpos_uncons (s: seq A) (i: 'J_s): 'J_((head_safe i)::(behead s)).
Proof. by case: s i => [[]|]//. Defined.
Lemma seqpos_uncons_correct (s: seq A) (i: 'J_s): i = seqpos_uncons i :> nat.
Proof. case: s i => //-[]//. Qed.

Definition seqpos_split (s s': seq A): 'J_(s ++ s') -> 'J_s + 'J_s'.
Proof. by move => /(cast_ord (size_cat _ _))/split. Defined.
Lemma seqpos_split_correct_lower (s s': seq A) (i: 'J_(s ++ s')): i < size s -> forall n, seqpos_split i = inl n <-> i = n :> nat.
Proof. Admitted.
Lemma seqpos_split_correct_upper (s s': seq A) (i: 'J_(s ++ s')): i >= size s -> forall n, seqpos_split i = inl n <-> i - (size s) = n :> nat.
Proof. Admitted.

Definition seqpos_unsplit (s s': seq A): ('J_s + 'J_s') -> 'J_(s++s').
Proof. by move => /unsplit/(cast_ord (sym_eq (size_cat _ _))). Defined.
Lemma seqpos_unsplit_correct_left (s s': seq A) (i: 'J_s):  seqpos_unsplit (inl (B:='J_s') i) = i :> nat.
Proof. Admitted.
Lemma seqpos_unsplit_correct_right (s s': seq A) (i: 'J_s'):  seqpos_unsplit (inr (A:='J_s) i) = i+(size s) :> nat.
Proof. Admitted.

Definition seq0 (x: A) (s: seq A): 'J_(x::s).
Proof. by move => /=; eexists ord0. Defined.
Lemma seq0_correct (x: A) (s: seq A): seq0 x s = 0 :> nat.
Proof. by done. Qed.

Definition seq_cons (x: A) (s: seq A): 'J_s -> 'J_(x::s).
Proof. move => -[n le]; by eexists n.+1; apply/le. Defined.
Lemma seq_cons_correct (x: A) (s: seq A) (i: 'J_s) : seq_cons x i = i.+1 :> nat.
Proof. by case: s i => [[]|_ _ []]//. Qed.


(* Another useful induction lemma. This one allows us to do an induction on both a sequence and a position of the sequence *)
Lemma size_ind s i (P: forall (s: seq A) (i: 'J_s), Type) :
  (forall x (s': seq A), P (x::s') (seq0 x s')) ->
  (forall x s' j, P s' j -> P (x::s') (seq_cons x j)) -> 
  P s i.
Proof.
move => HInit Hrec.
elim: s i => [|x s IHs [n le]]; first by case.
case: n le => [le|n le {HInit}];
  first by rewrite (bool_irrelevance le (ltn_ord ord0)); apply: HInit.
have ln: n < size s by done.
by move: (IHs (Ordinal ln)) => /(Hrec x) /=; rewrite (bool_irrelevance le ln).
Qed.

Fixpoint nth_safe (s: seq A) (n: 'J_s): A.
Proof.
move: n => -[n p]; case: n s p => [|n]; (case; [done | idtac]).
- exact.
- move => x s le; apply: (nth_safe s); by exists n.
Defined.
Lemma nth_safe_is_nth (d: A) (s: seq A) (n: 'J_s): nth_safe n = nth d s n.
Proof. elim/size_ind: n => {s}; by move => // x s -[] Hrec /=. Qed.

Lemma nth_safeQ (s: seq A) (x: A): List.In x s <-> exists i :'J_s, nth_safe i = x.
Proof.
split.
- elim: s => // a s IHs.
  case => [->|/IHs-[[n le] eqnx]]; first by exists ord0.
  by unshelve eexists (Ordinal (m:=n.+1) _).

- by move => []; elim/size_ind => {s} [x' s | x' s [n le] /= Hrec /Hrec]; [left | right].
Qed.

Variant seqpos_split_spec (s s': seq A) (i: 'J_(s ++ s')) : 'J_s + 'J_s' -> bool -> Type :=
  | SeqposSplitLo (j : 'J_s)  of nth_safe i = nth_safe j     : seqpos_split_spec i (inl _ j) true
  | SeqposSplitHi (k : 'J_s') of nth_safe i = nth_safe k     : seqpos_split_spec i (inr _ k) false.

Lemma seqpos_splitP (s s': seq A) (i : 'J_(s ++ s')) : seqpos_split_spec i (seqpos_split i) (i < size s).
Proof.
  have x: A by move: s s' i; do 2!case => [|?]; do 1?case.
  set lt_i_m := i < (size s); rewrite /seqpos_split/split.
  case: {-}_ lt_i_m / ltnP => jk; constructor; rewrite !(nth_safe_is_nth x) nth_cat;
      by [rewrite jk|rewrite ltnNge jk].
Qed.

Definition filter_ord p (s: seq A) (i: 'J_(filter p s)): 'J_s.
Proof.
  elim: s i => [[] //|x s IHs].
  case/boolP: (p x) => /= [-> | /negbTE -> /IHs/(seq_cons x) //].
  rewrite -cat1s => i.
  case/seqpos_split: {-}(i) => [_|];
  [by move => /=; eexists (ord0)|by (move => /IHs/(seq_cons x))].
Defined.
End SeqPos.
