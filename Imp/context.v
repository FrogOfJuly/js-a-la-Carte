
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

    

(* 

------------------------- header.v

Elpi TemplateSection 
Section js_feature_functor. 

Variables exp : Type.

Variable open_rec : nat -> (e : exp) -> exp -> exp.

#[induction=e, hints=[???]] (* need some way to remember when to do induction. Maybe not like this but by number?*)
Elpi AttemptProof (open_rec).


Elpi TemplateSection 
End js_feature_functor. 


------------------------- exp_lam.v

#[template=js_feature_functor]
Elpi FollowTemplateSection
Section exp_lam.

(* Defines all variables from the template *)

Inductive exp_lam : Type := 
        | ab : exp -> exp_lam
        | app : exp -> exp -> exp_lam
        | bvar : nat -> exp_lam
.


Context `{Hretr : retract exp_lam exp}.

Elpi ProofObligation (Hretr).

#[extends = exp] (* should it be a variable name or a "represents_as" name? Should it generate retract context decl? *)
Elpi RegisterTypeExtension (exp_lam).

(* SpecializeType open_rec exp_lam := searches for Variable open_rec, checks if it is marked with AttemptProof and replaces corresponding argument type with second argument *)
Definition open_rec_lam : ltac:(elpi SpecializeType open_rec exp_lam). (* picks extension *)
Proof.
intros until e. (* from AttemptProof? *)
elpi Induction e. (* destruct + variable calls on recursive occurrences. Maybe something like "specialized" inductive principle could be generated beforehand? Should it clear variable from context? *)
...
Defined. (* to be transparent *)

End exp_lam.

------------------------- language.v

[extensions(exp_lam, exp_ite, ...)]
Elpi Assemble signals.



*)