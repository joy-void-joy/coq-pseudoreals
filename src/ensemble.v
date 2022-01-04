From mathcomp Require Import ssreflect ssrnat seq ssrbool ssrfun eqtype fintype.
From Pseudoreals Require Import list.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We need our own version of ensembles as images of functions, as the
   standard construction of Coq would violate strict positivity.
*)
Section EnsembleG.
Inductive EnsembleG (A: Type) :=
|mkEnsembleG {T: Type} of (T -> A).

(* let us formalize set theories' operations *)

Definition emptyg {A: Type} :=  (mkEnsembleG A (False_rect _)).
Definition singletong {A: Type} x :=  (mkEnsembleG A (unit_rect _ x)).
Definition pairg {A: Type} x y :=  (mkEnsembleG A (bool_rect _ x y)).
Definition uniong {A: Type} (a b: EnsembleG A) := let: (mkEnsembleG _ f, mkEnsembleG _ f') := (a, b) in mkEnsembleG A (sum_rect _ f f').

Definition in_ensembleg {A: Type} (e: EnsembleG A) x := let: mkEnsembleG _ f := e in exists y, f y = x.
Definition ensembleg_eq {A: Type} (e e': EnsembleG A) := forall x, in_ensembleg e x <-> in_ensembleg e' x.

Definition anyg {A: Type} (P: A -> Prop) (e: EnsembleG A) := exists i, in_ensembleg e i /\ P i.
Definition mapg {T T': Type} (f: T -> T') (e:EnsembleG T): EnsembleG T' := let: (mkEnsembleG _ f') := e in mkEnsembleG _ (f \o f').

Inductive cut_set {A: Type} (P: A -> Prop): Type :=
|cut_intro (x: A) of P x.
Definition cut_set_strip {A: Type} {P: A -> Prop} (x: cut_set P): A := let: cut_intro v _ := x in v.
(* This might feel like a cause for concern. It is not, insofar that Coq restricts what type we are able to naive cut on.
   Namely, we are not allowed to perform a naive cut on other ensembles.
*)
Definition naive_cut {A: Type} (P: A -> Prop) := mkEnsembleG A (cut_set_strip (P := P)).
(* Which is why we require a hack to cut ensembles *)
Definition ensembleg_cut {A: Type} (e: EnsembleG A) (P: A -> Prop) := naive_cut (fun x => P x /\ in_ensembleg e x).

End EnsembleG.

(*
 The above definition is not very usable.
While it is theoritically possible to formalize any set, finite or infinite, in it, it makes most of simple sequences not computable, as Coq has poor support for eta-expension
  So we will mostly use a hybrid definition, that can directly state the ensemble is finite
*)
Section Ensemble.
Inductive Ensemble (A: Type) :=
|finEnsemble of seq A
|infinEnsemble of EnsembleG A.
Arguments finEnsemble {A}.
Arguments infinEnsemble {A}.

Coercion ensemble_of_seq {A: Type} (s: seq A) := finEnsemble s.
Coercion ensembleg_of_ensemble {A: Type} (e: Ensemble A): EnsembleG A := match e with
|finEnsemble s => mkEnsembleG A (nth_safe s)
|infinEnsemble e => e
end.

Definition in_ensemble {A: Type} (e: Ensemble A) x := match e with
|finEnsemble s => List.In x s
|infinEnsemble e => in_ensembleg e x
end.
Definition ensemble_eq {A: Type} (e e': Ensemble A) := forall x, in_ensemble e x <-> in_ensemble e' x.
Notation "e ~= e'" := (ensemble_eq e e')(at level 90).

Definition map {T T': Type} (f: T -> T') (e: Ensemble T): Ensemble T' := match e with
|finEnsemble s => finEnsemble [seq f i | i <- s]
|infinEnsemble e => infinEnsemble (mapg f e)
end.

Definition any_ensemble {A} (P: A -> Prop) (e: Ensemble A) := match e with
|finEnsemble s => any P s
|infinEnsemble e => anyg P e
end.

Definition union {A: Type} (e e': Ensemble A) := match e, e' with
|finEnsemble s, finEnsemble s' => finEnsemble (s ++ s')
|a, b => infinEnsemble (uniong a b)
end.

Section EquivalenceG.
Definition correctg {A A': Type} (f: Ensemble A -> Ensemble A') (e: Ensemble A)  := f e ~= f (infinEnsemble e).

Lemma mapg_correct {A A'} (f: A -> A') (e: Ensemble A): correctg (map f) e.
Proof.
  case: e => // s x'.
  split => /= [/nth_safeQ-[[m lt] <-]|[[m lt <-]]].
  - have x: A by case: s lt; done.
    exists (cast_ord (size_map _ _) (Ordinal lt)).
    rewrite (nth_safe_is_nth x) (nth_safe_is_nth x') /=.
    by apply/sym_eq/nth_map; by rewrite -(size_map f).

  - apply/nth_safeQ.
    exists (cast_ord (sym_eq (size_map _ _)) (Ordinal lt)).
    have x: A by case: s lt; done.
    rewrite (nth_safe_is_nth x) (nth_safe_is_nth x') /=.
    by apply/nth_map.
Qed.

Lemma anyg_correct {A} (P: A -> Prop) (e: Ensemble A) : any_ensemble P e <-> anyg P e.
  case: e => // s.
  split => [|[x [[i]] <-]].
  - elim: s => // h s IHs.
    case => [|/IHs-[x [[i eqx]]]];
      first by exists h; split; by do? eexists ord0.
    by exists x; split => //; unshelve eexists (seq_cons h s i); case: i eqx => /=.

  - elim/(size_ind s): i => [{}x {}s|{}x {}s [n le] IHs /IHs];
    by [left | right].
Qed.

Lemma inEnsembleg_correct {A: Type} (e: Ensemble A) x :  in_ensemble e x <-> in_ensembleg e x.
case: e => [s|]; last by done.
split => [|[i] <-].
- elim: s => // a s IHs [<- /=|/IHs-[[n le] eqnx]]; by [exists ord0|eexists (Ordinal (m:=n.+1) _) => /=; exact: eqnx].
- elim/(size_ind s): i => [{x s} x s|{x s} x s [n]]; by [left | right].
Qed.

Lemma inEnsemblegP {A: eqType} (s: seq A) x : reflect (in_ensembleg s x) (x \in s).
Proof. apply/(equivP (inP _ _))/(inEnsembleg_correct s x). Qed.

Lemma inEnsembleP {A: eqType} (s: seq A) x : reflect (in_ensemble s x) (x \in s).
Proof. exact: inP. Qed.

Lemma ensemble_irrevelance {A: Type} (s: seq A) : s ~= infinEnsemble s.
Proof. split => [/inEnsembleg_correct //| ?]; exact/inEnsembleg_correct. Qed.

Lemma emptyg_correct {A: Type}: [::] ~= infinEnsemble (emptyg (A := A)).
Proof. split; by case. Qed.

Lemma singletong_correct {A: Type} (x: A): [:: x] ~= infinEnsemble (singletong x).
Proof. split => [[] // <-| [[]] <-]; by [exists tt | left]. Qed.

Lemma  pairg_correct {A: Type} (x y: A): [:: x; y] ~= infinEnsemble (pairg x y).
Proof. split => [[|[|[]]] -> | [[]] <-]; by [exists true| exists false | left | right; left]. Qed.

Lemma uniong_correct {A: Type} (e e': Ensemble A): union e e' ~= infinEnsemble (uniong e e').
  case: e => // e; case: e' => // e'; split => /= [/nth_safeQ-[sum]|[y <-]];
    first by case/seqpos_splitP: (sum) => jk -> <- ; [exists (inl jk) | exists (inr jk)].
  apply/nth_safeQ; exists (seqpos_unsplit y).
  case: y => /= jk; rewrite !(nth_safe_is_nth x) nth_cat /=; first by case: jk => /= n ->.
  by rewrite ltnNge leq_addr -addnBAC //= subnn add0n.
Qed.
