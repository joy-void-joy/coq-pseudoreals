(* ssrbool's reflect is designed to work on mostly functional predicate.
   As we will be using some inductive predicates, we will need a way to transform ssrbool's lemmas
   about reflection to also hold on properties.
   This allows us for instance to transform:

     orP: reflect (b \/ b') (b || b')

  into

    orTP: reflect P b' -> reflect (b \/ P) (b || b').
*)
Require Import ssreflect ssrbool.

Section functor.
Context {P: Prop}.
Context {b c: bool}.

(* A transformation from props to props is a functor if it only depends on its truth value *)
Definition functor (H: Prop -> Prop) := forall (Px Qx: Prop), (Px -> Qx) -> H Px -> H Qx.

Lemma functorP {H: Prop -> Prop} (functor: functor H): reflect P b -> reflect (H b) c -> reflect (H P) c.
move => rpb rhbc.
case: rhbc => [|nHb]; constructor;
  first by apply: functor; first exact/rpb.
move => HP; apply: nHb.
apply: functor; last exact/HP.
exact/introT.
Qed.

Lemma orT P': functor (or P').
Proof. move => Px Qx PxQx; by case; eauto. Qed.
Definition orTP {P'} := functorP (orT P').
End functor.