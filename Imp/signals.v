From Imp Require Import header_extensible.
From Imp Require Import elpi_shenanigans.

(* Feature functors *)
From Imp Require Import exp_ite exp_lam exp_mut exp_err.
(* Interaction functors *)
From Imp Require Import int_lam_err int_ite_err int_mut_err.

From elpi Require Import elpi.


Inductive exp : Type := 
    | In_exp_lam : exp_lam exp -> exp
    | In_exp_ite : exp_ite exp -> exp
    | In_exp_mut : exp_mut exp -> exp
    | In_exp_err : exp_err exp -> exp
.

#[represeted_as = exp]
Elpi RegisterRepresented (exp).


Elpi Tactic exact_constructor.
Elpi Accumulate lp:{{
    solve (goal _ _ Ty _ [str IndName] as G) GL :- 
        % locate inductive type
        std.assert! (coq.locate IndName (indt IndTyGRef)) "not an inductive type", !,
        % locate constructors Constr of inductive type IndTyGRef
        coq.env.indt IndTyGRef _ _ _ _ Constr _,
        % find corresponding terms(ConstrTerms) by querying environment(env.global) for constructor symbols
        % by relating output `r` to `indc c`
        std.map Constr (c\ r\ coq.env.global (indc c) r) ConstrTerms,
        % find their types by typechecking found terms by coq.typecheck
        % saving them into ConstrTypes
        std.map ConstrTerms (kt\ r\ coq.typecheck kt r _) ConstrTypes,
        % relate constructors to their types them together to establish correspondence
        % by zipping them together
        std.zip ConstrTerms ConstrTypes TermTypes,
        % find term corresponding to goal type
        std.assert! (std.mem TermTypes (pr C Ty)) "can't solve with exact constructors",
        % use it
        refine C G GL.
    solve (goal _ _ Ty _ [str IndName] as _G) _GL :- 
        coq.say "Failed to solve" Ty  "with exact constructors of type" IndName, 
        coq.ltac.fail _ "fail".
}}.

Ltac derive_exp_retract_instance := match goal with 
    | [|- retract ?X exp] => exact (@Build_retract X exp
                                    ltac:(elpi exact_constructor exp)
                                    ltac:(intros x; destruct x; try (apply Some; assumption); exact None)
                                    ltac:(simpl; intros; trivial)
                                    ltac:(simpl; intros x y; destruct y; inversion 1; easy)
                            )
end.

#[refine] Global Instance retract_exp_exp_lam : retract (exp_lam exp) exp := ltac:(derive_exp_retract_instance). Defined.
#[refine] Global Instance retract_exp_exp_ite : retract (exp_ite exp) exp := ltac:(derive_exp_retract_instance). Defined.
#[refine] Global Instance retract_exp_exp_mut : retract (exp_mut exp) exp := ltac:(derive_exp_retract_instance). Defined.
#[refine] Global Instance retract_exp_exp_err : retract (exp_err exp) exp := ltac:(derive_exp_retract_instance). Defined.


#[represeted_as = retract_exp_exp_lam]
Elpi RegisterRepresented (retract_exp_exp_lam).


Fixpoint open_rec (k : nat) (u : exp) (e : exp) : exp := 
    match e with 
        (* | In_exp_lam e => open_rec_lam _ open_rec k u e *)
        | In_exp_lam e => ltac:(elpi specialize_from_section open_rec_lam) k u e
        | In_exp_ite e => open_rec_ite _ open_rec k u e
        | In_exp_mut e => open_rec_mut _ open_rec k u e
        | In_exp_err e => open_rec_err _ open_rec k u e
    end
.

Check open_rec_lam.

Definition open_rec_lam' := ltac:(exact (open_rec_lam exp open_rec)).

Check open_rec_lam'.


Inductive lc' : nat -> exp -> Prop := 
    | lc_in_lam n e : lc'_lam _ lc' n e -> lc' n e
    | lc_in_ite n e : lc'_ite _ lc' n e -> lc' n e
    | lc_in_mut n e : lc'_mut _ lc' n e -> lc' n e
    | lc_in_err n e : lc'_err _ lc' n e -> lc' n e
.

(* Check lc'_lam. *)
Elpi Command ReadAttr.
Elpi Accumulate lp:{{

    main [] :- 
        coq.say {{exp_lam}}.
}}.

(* Elpi ReadAttr. *)


Inductive value : exp -> Prop := 
    | value_in_lam (e : exp) : value_lam _ lc' e -> value e
    | value_in_ite (e : exp) : value_ite _ e -> value e
    | value_in_mut (e : exp) : value_mut _ e -> value e
    | value_in_err (e : exp) : value_err _ e -> value e
.
(* 
#[arguments(raw)] Elpi Command build_retract_lc_rev_type.
Elpi Accumulate lp:{{ 
    main [trm LcExt, trm ExpExt] :- 
        std.assert-ok! (coq.typecheck ExpExt TyExp) "argument illtyped",
        std.assert-ok! (coq.typecheck LcExt {{ forall (exp : Type), retract_f lp:{{ ExpExt }} exp -> (nat -> exp -> Prop) -> nat -> exp -> Prop }}) "argument illtyped",
        coq.say "Ok".

        
 }}.

Elpi build_retract_lc_rev_type (lc'_ite) (exp_ite).
Elpi build_retract_lc_rev_type (lc'_mut) (exp_mut).
Elpi build_retract_lc_rev_type (lc'_ite) (exp_ite). 

*)

Definition retract_lc_revT exp_ext lc'_ext { retr : retract_f exp_ext exp} : Prop :=
    forall (n : nat) (e : exp_ext exp), lc' n (inj e) -> lc'_ext retr lc' n (inj e). 

Definition retract_lc_rev_lam : retract_lc_revT exp_lam (@lc'_lam exp) := ltac:(intros n e; inversion 1; easy).
Definition retract_lc_rev_ite : retract_lc_revT exp_ite (@lc'_ite exp) := ltac:(intros n e; inversion 1; easy).
Definition retract_lc_rev_mut : retract_lc_revT exp_mut (@lc'_mut exp) := ltac:(intros n e; inversion 1; easy).
Definition retract_lc_rev_err : retract_lc_revT exp_err (@lc'_err exp) := ltac:(intros n e; inversion 1; easy).

Definition retract_open_rec_rev exp_ext open_rec_ext  { retr : retract_f exp_ext exp } : Prop :=
    forall (n : nat) s (e : exp_ext exp), open_rec n s (inj e) = open_rec_ext retr open_rec n s e.

Definition retract_open_rec_rev_lam : retract_open_rec_rev exp_lam (@open_rec_lam exp) := ltac:(intros; easy).
Definition retract_open_rec_rev_ite : retract_open_rec_rev exp_ite (@open_rec_ite exp) := ltac:(intros; easy).
Definition retract_open_rec_rev_mut : retract_open_rec_rev exp_mut (@open_rec_mut exp) := ltac:(intros; easy).
Definition retract_open_rec_rev_err : retract_open_rec_rev exp_err (@open_rec_err exp) := ltac:(intros; easy).


Fixpoint lc_weaken   : forall s n m, n <= m -> lc' n s -> lc' m s.
inversion 2; subst.
- apply (lc_weaken_lam exp _ lc_weaken lc_in_lam _) with (n := n); easy.
- apply (lc_weaken_ite exp _ lc_weaken lc_in_ite _) with (n := n); easy.
- apply (lc_weaken_mut exp _ lc_weaken lc_in_mut _) with (n := n); easy.
- apply (lc_weaken_err exp _ lc_weaken lc_in_err _) with (n := n); easy.
Qed.

Fixpoint open_rec_lc : forall s t n, lc' 0 s -> lc' (S n) t -> lc' n (open_rec n s t).
Proof.
inversion 2; subst.
- apply (open_rec_lc_lam exp open_rec retract_open_rec_rev_lam lc' open_rec_lc lc_weaken lc_in_lam); easy.
- apply (open_rec_lc_ite exp open_rec retract_open_rec_rev_ite lc' open_rec_lc lc_in_ite); easy.
- apply (open_rec_lc_mut exp open_rec retract_open_rec_rev_mut lc' open_rec_lc lc_in_mut); easy.
- apply (open_rec_lc_err exp open_rec retract_open_rec_rev_err lc' open_rec_lc lc_in_err); easy.
Qed.

Fixpoint value_lc : forall v, value v -> lc' 0 v.
Proof.
    inversion 1; subst.
    - apply (value_lc_lam _ _); easy.
    - apply (value_lc_ite _ _ lc_in_ite); easy.
    - apply (value_lc_mut _ _ lc_in_mut); easy.
    - apply (value_lc_err _ _); easy.
Qed.

Inductive tag := 
    | In_tag_lam : tag_lam -> tag
    | In_tag_ite : tag_ite -> tag
    | In_tag_mut : tag_mut -> tag
    | In_tag_err : tag_err -> tag
.

Ltac derive_tag_retract_instance := match goal with 
    [|- retract ?X tag] => exact (@Build_retract X tag
                                    ltac:(elpi exact_constructor tag)
                                    ltac:(intros x; destruct x; try (apply Some; assumption); exact None)
                                    ltac:(simpl; intros; trivial)
                                    ltac:(simpl; intros x y; destruct y; inversion 1; congruence)
    )
end.

#[refine] Global Instance retract_tag_tag_lam : retract tag_lam tag := ltac:(derive_tag_retract_instance). Defined. 
#[refine] Global Instance retract_tag_tag_ite : retract tag_ite tag := ltac:(derive_tag_retract_instance). Defined.
#[refine] Global Instance retract_tag_tag_mut : retract tag_mut tag := ltac:(derive_tag_retract_instance). Defined.
#[refine] Global Instance retract_tag_tag_err : retract tag_err tag := ltac:(derive_tag_retract_instance). Defined.

Inductive tag_of : exp -> tag -> Prop := 
    | tag_of_in_lam e t: tag_of_lam _ _ e t -> tag_of e t
    | tag_of_in_ite e t: tag_of_ite _ _ e t -> tag_of e t
    | tag_of_in_mut e t: tag_of_mut _ _ e t -> tag_of e t
    | tag_of_in_err e t: tag_of_err _ _ e t -> tag_of e t 
.

Elpi Command RetractProp.
Elpi Accumulate lp:{{
    pred type->rng i:term o:(list term).
    type->rng {{ lp:A -> lp:B }} (A::Rng) :- type->rng B Rng.
    type->rng T [T].



    main [trm P, trm Pinj] :- 
        std.assert-ok! (coq.typecheck P P_Ty) "argument illtyped",
        type->rng P_Ty P_Dec,
        coq.say "Look P:" P_Dec,
        std.assert-ok! (coq.typecheck Pinj Pinj_Ty) "argument illtyped",
        type->rng Pinj_Ty Pinj_Dec,
        coq.say "Look P_inj" Pinj_Dec.
    main Args :-
        coq.error "Called with wrong arguments:" Args _.
}}.

(* Check tag_of_lam. *)

Elpi RetractProp (tag_of) (@tag_of_lam exp retract_exp_exp_lam tag retract_tag_tag_lam).

Lemma retract_tag_of_lam : forall (t : tag_lam) (e : exp_lam exp), tag_of (inj e) (inj t) <-> tag_of_lam _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma retract_tag_of_ite : forall (t : tag_ite) (e : exp_ite exp), tag_of (inj e) (inj t) <-> tag_of_ite _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma retract_tag_of_mut: forall (t : tag_mut) (e : exp_mut exp), tag_of (inj e) (inj t) <-> tag_of_mut _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma retract_tag_of_err : forall (t : tag_err) (e : exp_err exp), tag_of (inj e) (inj t) <-> tag_of_err _ _ (inj e) (inj t).
Proof.
    intros t e.
    split.
    - inversion 1; easy.
    - constructor; easy.
Qed.

Lemma tag_of_decidable e t : ~tag_of e t \/ tag_of e t.
Proof.
    destruct e; destruct t.
    all: try (rewrite retract_tag_of_lam; apply tag_of_decidable_lam).
    all: try (rewrite retract_tag_of_ite; apply tag_of_decidable_ite).
    all: try (rewrite retract_tag_of_mut; apply tag_of_decidable_mut).
    all: try (rewrite retract_tag_of_mut; apply tag_of_decidable_mut).
    all: try (rewrite retract_tag_of_err; apply tag_of_decidable_err).
    all: left; inversion 1; inversion H0.
Qed.

From Imp Require Import context.

Definition VarEnv := Env (sig value).

Record Ctx := mkCtx {
        store : VarEnv;
}.

#[refine] Global Instance ctx_supports_store : hasProj Ctx VarEnv := {
    get_proj := store;
    set_proj := (fun x c => mkCtx x);
}.
Proof.
    - intros. easy.
    - intros. destruct c. simpl. easy.
Defined.

Inductive step : Ctx -> exp -> Ctx -> exp -> Prop := 
    | step_in_lam (c : Ctx) s c' s' : step_lam _ open_rec value _ step c s c' s' -> step c s c' s'
    | step_in_ite (c : Ctx) s c' s' : step_ite _ _                step c s c' s' -> step c s c' s'
    | step_in_mut (c : Ctx) s c' s' : step_mut _ _ _              step c s c' s' -> step c s c' s'
    | step_in_err (c : Ctx) s c' s' : step_err _ _                step c s c' s' -> step c s c' s'
    (* interactions *)
    | step_in_lam_err (c : Ctx) s c' s' : step_int_lam_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
    | step_in_ite_err (c : Ctx) s c' s' : step_int_ite_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
    | step_in_mut_err (c : Ctx) s c' s' : step_int_mut_err _ value _ tag_of _ step c s c' s' -> step c s c' s'
.

Definition lc := lc' 0.
Definition open := open_rec 0.

Fixpoint preservation : forall c e c' e', 
    lc e -> 
    step c e c' e' -> 
    lc e'. 
Proof. 
    intros c e c' e'.
    unfold lc in *.
    induction 2.
    - apply (preservation_lam exp open_rec lc' open_rec_lc lc_in_lam retract_lc_rev_lam value Ctx step preservation c s c' s'); easy.
    - apply (preservation_ite exp lc' lc_in_ite retract_lc_rev_ite Ctx step preservation c s c' s'); easy.
    - apply (preservation_mut exp lc' lc_in_mut retract_lc_rev_mut value value_lc Ctx step preservation c s c' s'); easy.
    - apply (preservation_err exp lc' lc_in_err retract_lc_rev_err Ctx step preservation c s c' s'); easy.
    (* interactions *)
    - apply (preservation_lam_err exp lc' lc_in_err retract_lc_rev_lam retract_lc_rev_err value value_lc tag tag_of Ctx step preservation c s c' s'); easy.
    - apply (preservation_ite_err exp lc' lc_in_err retract_lc_rev_ite retract_lc_rev_err value value_lc tag tag_of Ctx step preservation c s c' s'); easy.
    - apply (preservation_mut_err exp lc' lc_in_mut lc_in_err retract_lc_rev_mut value tag tag_of Ctx step preservation c s c' s'); easy.
Defined.

