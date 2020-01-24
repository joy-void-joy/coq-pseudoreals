Load list.

(* We need our own version of ensembles as images of functions, as the
   standard construction of Coq would violate strict positivity.
*)
Section EnsembleG.
Inductive EnsembleG (A: Type) :=
|mkEnsembleG {T: Type} of (T -> A).

Definition emptyg {A: Type} :=  (mkEnsembleG A (False_rect _)).
Definition singletong {A: Type} x :=  (mkEnsembleG A (unit_rect _ x)).
Definition pairg {A: Type} x y :=  (mkEnsembleG A (bool_rect _ x y)).
Definition uniong {A: Type} (a b: EnsembleG A) := let: (mkEnsembleG _ f, mkEnsembleG _ f') := (a, b) in mkEnsembleG A (sum_rect _ f f').

Definition mapg {T T': Type} (f: T -> T') (e:EnsembleG T): EnsembleG T' := let: (mkEnsembleG _ f') := e in mkEnsembleG _ (f \o f').
Definition in_ensembleg {A: Type} (e: EnsembleG A) x := let: mkEnsembleG _ f := e in exists y, f y = x.
Definition ensembleg_eq {A: Type} (e e': EnsembleG A) := forall x, in_ensembleg e x <-> in_ensembleg e' x.
End EnsembleG.

(*
 This definition is not very usable. While it allows for any games, it does not make interesting games such as 0 or * computable.
  So we will mostly use a hybrid definition, that can state the ensemble is finite
*)
Section Ensemble.
Inductive Ensemble (A: Type) :=
|finEnsemble of seq A
|infinEnsemble of EnsembleG A.

Coercion ensemble_of_seq {A: Type} (s: seq A) := finEnsemble _ s.
Coercion ensembleg_of_ensemble {A: Type} (e: Ensemble A): EnsembleG A := match e with
|finEnsemble s => mkEnsembleG A (nth_safe s)
|infinEnsemble e => e
end.

Definition map {T T': Type} (f: T -> T') (e: Ensemble T): Ensemble T' := match e with
|finEnsemble s => finEnsemble _ [seq f i | i <- s]
|infinEnsemble e => infinEnsemble _ (mapg f e)
end.

Definition in_ensemble {A: Type} (e: Ensemble A) x := match e with
|finEnsemble s => List.In x s
|infinEnsemble e => in_ensembleg e x
end.
Definition ensemble_eq {A: Type} (e e': Ensemble A) := forall x, in_ensemble e x <-> in_ensemble e' x.
Notation "e ~= e'" := (ensemble_eq e e')(at level 90).

Section EquivalenceG.
Lemma inEnsemblegQ {A: Type} (s: seq A) x : in_ensembleg s x <-> List.In x s.
split.
- by elim: s => [[[//]]|a s IHs [[[|n le eqnx]]] /=]; [by left |  right; apply: IHs; eexists (Ordinal (m:=(n)) _); exact: eqnx].
- elim: s => // a s IHn [<-|/IHn-[[n le eqnx]]]; by [exists ord0 | eexists (Ordinal (m:=n.+1) _); exact: eqnx].
Qed.

Lemma inEnsemblegP {A: eqType} (s: seq A) x : reflect (in_ensembleg s x) (x \in s).
suff ref: reflect (List.In x s) (x \in s) by apply/(equivP ref)/(iff_sym (inEnsemblegQ _ _ )).
exact: inP.
Qed.

Lemma inEnsembleP {A: eqType} (s: seq A) x : reflect (in_ensemble s x) (x \in s).
Proof. exact: inP. Qed.

Lemma ensemble_irrevelance {A: Type} (s: seq A) : s ~= infinEnsemble _ s.
Proof. split; by move => /inEnsemblegQ. Qed.

Lemma emptyg_correct {A: Type}: [::] ~= infinEnsemble _ (emptyg (A := A)).
Proof. 
Proof. split; by case. Qed.

Lemma singletong_correct {A: Type} (x: A): [:: x] ~= infinEnsemble _ (singletong x).
Proof. split => [[] // <-| [[]] <-]; by [exists tt | left]. Qed.

Lemma  pairg_correct {A: Type} (x y: A): [:: x; y] ~= infinEnsemble _ (pairg x y).
Proof. split => [[|[|[]]] -> | [[]] <-]; by [exists true| exists false | left | right; left]. Qed.

Definition union {A: Type} (e e': Ensemble A) := match e, e' with
|finEnsemble s, finEnsemble s' => finEnsemble _ (s ++ s')
|a, b => infinEnsemble _ (uniong a b)
end.
