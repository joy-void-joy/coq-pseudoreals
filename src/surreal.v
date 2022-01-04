From mathcomp Require Import ssreflect ssrnat fintype ssrbool ssrfun eqtype finfun seq.
From Pseudoreals Require Import list ensemble.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Saddly we cannot just declare game as two ensembles of game. If we did, Coq would not be able to infer the very useful induction lemma:

  all P l -> all P r -> P {l | r}

So we need to define a MetaEnsemble, that will contain different level of ensembles, like {2, {3}, {4, {5, 6}}}
*)
Inductive MetaEnsemble (A: Type) :=
|MetaEnsemble_node of Ensemble (MetaEnsemble A)
|MetaEnsemble_leaf of A.
Coercion metaensemble_of_ensemble {A: Type} (e: Ensemble (MetaEnsemble A)): MetaEnsemble A := MetaEnsemble_node e.

Lemma MetaEnsemble_all_ind {A: Type} (P: MetaEnsemble A -> Prop): 
  (forall a, P (MetaEnsemble_leaf a)) -> 
  (forall e, all P e -> P (MetaEnsemble_node e)) ->
  forall e, P e.
Admitted.

Inductive Game :=
|mkGame of MetaEnsemble Game & MetaEnsemble Game.

Coercion ensembleg_of_game (e: Game): MetaEnsemble Game := MetaEnsemble_leaf e.

Notation "{}" := (MetaEnsemble_node (finEnsemble [::])).
Notation "{ l | r }" := (mkGame l r) (at level 0, format "'[' { l | r } ']'", l at level 99).
Notation "{ l | }" := {l | {}} (at level 0, format "{ l | }", l at level 99).
Notation "{ | r }" := {{} | r} (at level 0, format "{ | r }").
Notation "{|}" := {{} | {}} (at level 0, format "{|}").

Fixpoint game_of_nat n := if n is m.+1 then {(game_of_nat m) | } else {|}.