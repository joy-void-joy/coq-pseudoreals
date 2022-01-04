From mathcomp Require Import ssreflect ssrbool.
(* ssrbool's reflect is designed to work on mostly functional predicate.
   As we will be using some inductive predicates, we will need a way to transform ssrbool's lemmas
   about reflection to also hold on properties.
   For now we will use property functor, so instead of using

     `orP: reflect (b \/ b') (b || b')`


  we will use orT which allows us to transform `reflect (P \/ P') c` into `reflect (b \/ P') c` provided `reflect P b`
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section functor.
Variables (P: Prop) (b c: bool).
Section DefFunctor.
Variables (H: Prop -> Prop).
Definition functor := forall (Px Qx: Prop), (Px -> Qx) -> H Px -> H Qx.
Hypotheses functor_H: functor.

(* A transformation from props to props is a functor if it only depends on its truth value *)
Lemma functor_iff: forall Px Qx, (Px <-> Qx) -> (H Px <-> H Qx).
Proof.
  move => Px Qx iff.
  split; by apply/functor_H => /iff.
Qed.

Lemma functorP: reflect P b -> reflect (H b) c -> reflect (H P) c.
Proof.
  move => rpb rhbc.
  apply/equivP; first exact: rhbc.
  by apply:functor_iff => //; apply: iff_sym; apply: Bool.reflect_iff.
Qed.
End DefFunctor.

Lemma functor_or P' : functor (or P').
Proof. move => Px Qx PxQx; by case; eauto. Qed.

Definition orT P' := functorP (functor_or (P':=P')).
End functor.
(* TODO: Do andT and others *)

Check orT.
