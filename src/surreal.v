Require Import ZArith.
From mathcomp Require Import ssreflect ssrnat fintype ssrbool ssrfun eqtype finfun seq.
Load ensemble.

Inductive Game :=
|mkGame of (Ensemble Game) & (Ensemble Game).
Coercion ensembleg_of_game (e: Game): Ensemble Game := [:: e].

Notation "{}" := (finEnsemble Game [::]).
Notation "{ l | r }" := (mkGame l r) (at level 0, format "'[' { l | r } ']'", l at level 99).
Notation "{ l | }" := {l | {}} (at level 0, format "{ l | }", l at level 99).
Notation "{ | r }" := {{} | r} (at level 0, format "{ | r }").
Notation "{|}" := {{} | {}} (at level 0, format "{|}").

Fixpoint game_of_nat n := if n is m.+1 then {(game_of_nat m) | } else {|}.
Fixpoint negative g := let: {l | r} := g in {map negative r | map negative l}.
Definition game_of_Z z := let: res := game_of_nat (Z.abs_nat z) in if Z.geb 0 z then res else negative res.
Coercion game_of_Z: Z >-> Game.
Fixpoint plus (a b: Game): Game := let: ({al | ar}, {bl | br}) := (a, b) in {union (map (plus b) al) (map (plus a) bl) | union (map (plus b) ar) (map (plus a) bl)}.
Definition x_plus_half (x: Z) := {x | x+1}.

-
