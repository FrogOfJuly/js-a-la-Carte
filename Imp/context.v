
From Stdlib Require Export FSets.FMapList.
From Stdlib Require Import Structures.OrderedTypeEx.

Module Import Env := Stdlib.FSets.FMapList.Make(Nat_as_OT).

Definition Env := Env.t.

Fact fresh_loc : forall {A} (e : Env A), exists l, Env.mem l e = false.
Proof.
    intros A e.
Admitted.

Class hasProj C X := {
    get_proj : C -> X;
    set_proj : X -> C -> C;
    set_idemp  : forall c x, get_proj (set_proj x c) = get_proj (set_proj x (set_proj x c));
    get_set_id : forall c, set_proj (get_proj c) c = c
}.

    

