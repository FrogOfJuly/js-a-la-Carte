From Stdlib Require Import String List Lia.

(* From Equations Require Import Equations. (*  Equations.Prop.DepElim. *) *)
Set Implicit Arguments.
Unset Strict Implicit.

(* Lemma solve_anything : forall (A : Type), A.
(* FIXME: That's technical, should not be used anywhere *)
Admitted. *)

Arguments eq_refl {A x}, {A} x.

(** ** Basic definitions  *)

Class retract X Y :=
  {
    retract_I : X -> Y ;
    retract_R : Y -> option X;
    retract_works : forall x, retract_R (retract_I x) = Some x;
    retract_tight : forall x y, retract_R y = Some x -> retract_I x = y
  }.

Arguments Build_retract {X} {Y}.

Lemma retract_inj {X Y} {R : retract X Y} x y :
  retract_I x = retract_I y -> x = y.
Proof.
  intros. enough (Some x = Some y) by congruence.
  now rewrite <- !retract_works, H.
Qed.

Instance retract_option X Y : retract X Y -> retract (option X) (option Y).
Proof.
  intros. unshelve eexists.
  - intros []. exact (Some (retract_I x)). exact None.
  - intros []. destruct (retract_R y). exact (Some (Some x)). exact None. exact (Some None).
  - intros []. cbn. now rewrite retract_works. reflexivity.
  - intros. cbn in *. destruct y.  destruct x.
    + destruct (retract_R y) eqn:E. inversion H. subst. clear H.
      eapply retract_tight in E. congruence. inversion H.
    + destruct (retract_R y) eqn:E. inversion H. inversion H.
    + inversion H. reflexivity.
Defined.

Definition lift {X Y Y'} `{retract Y Y'} (f : X -> Y) := (fun n => retract_I (f n)).
Notation inj := (retract_I).
Notation retr := (retract_R).

Notation retract_f F T := (retract (F T) T)%type.

Class Bundle (func : Type -> Type) (In : forall X, X -> func X -> Prop) := make_Bundle {}.
Existing Instance make_Bundle.

Definition get_In {func In} {bundle : @Bundle func In} := In.

Lemma congr_inj {X Y} `{retract X Y} {x y}:
  x = y -> inj x = inj y.
Proof.
  congruence.
Qed.



(* From elpi Require Import elpi.

Elpi Db exp_lam.db lp:{{
  % pred section_deps i:gref o:(list gref).
  
  % :name "section_deps.fail"
  % section_deps GRef _ :- coq.error "I don't know what" GRef "is!".
}}.

Elpi Command RegisterExtension'.
Elpi Accumulate Db exp_lam.db.
Elpi Accumulate lp:{{
  pred section_deps o:gref o:(list gref).
  
  main Args :-
    coq.say "RegisterExtension': Don't know what is this" Args.
}}.


Elpi Command RegisterExtension.
Elpi Accumulate Db exp_lam.db.
Elpi Accumulate lp:{{

  pred register_section_dep i:gref i:list gref.
  register_section_dep GR GRDep :- 
    Db = get-option "db",
    coq.say "Adding rule" TheNewRule.
    % coq.elpi.accumulate _ "exp_lam.db" (clause _ (before "section_deps.fail") TheNewRule).
  
  main [trm (global GRef)] :- 
    attributes A,
    coq.env.transitive-dependencies GRef _ TransDep,
    % coq.say "Transitive dependencies:" TransDep,
    coq.env.section SectionVarsL,
    std.filter SectionVarsL (x\ coq.gref.set.mem ( const x) TransDep) SectionVarsLRelevant,
    std.map SectionVarsLRelevant (x\ r\ r is const x) SectionVarsLRelevantGref,
    coq.parse-attributes A [
      att "extends" string,
      att "db" string,
    ] Opts.
  main [trm Arg] :- 
    attributes A,
    coq.parse-attributes A [
      att "extends" string,
    ] _Opts,
    coq.say "Registered extension" Arg "for" A.
  main Args :-
    coq.error "Called with wrong arguments:" Args _.
}}.

(* external func coq.env.term-dependencies term -> coq.gref.set. *)
Elpi Command RegisterExtensionInline.
Elpi Accumulate Db exp_lam.db.
Elpi Accumulate lp:{{
  pred register.
  register :- 
    coq.say "Skipped adding rule". 

  pred register_section_dep i:gref i:list gref.
  register_section_dep GR GRDep :- 
    TheNewRule = section_deps GR GRDep,
    _Db = get-option "db",
    coq.say "Adding rule" TheNewRule,
    coq.elpi.accumulate _ "exp_lam.db" (clause _ (before "section_deps.fail") TheNewRule).

  main [indt-decl I] :- !,
    coq.env.add-indt I Ind,
    coq.env.transitive-dependencies (indt Ind) _ TransDep,
    % coq.say "Transitive dependencies:" TransDep,
    coq.env.section SectionVarsL,
    std.filter SectionVarsL (x\ coq.gref.set.mem ( const x) TransDep) SectionVarsLRelevant,
    % coq.say "All section variables:" SectionVarsL,
    % coq.say "Used section dependencies:" SectionVarsLRelevant,
    std.map SectionVarsLRelevant (x\ r\ r is const x) SectionVarsLRelevantGref,
    attributes A,
    coq.parse-attributes A [
      att "extends" string,
      att "db" string,
    ] Opts.
    % % Should call Register extension here instead of `register`
    % (Opts =!=> register_section_dep (indt Ind) SectionVarsLRelevantGref).
  main [const-decl Id (some T) _Ar] :- !,
    std.assert-ok! (coq.typecheck T Ty) "This is ill-typed",
    % coq.say "Found this:" Id "," T "," Ar,
    coq.env.add-const Id T Ty _opaqueness _C,
    attributes A,
    coq.parse-attributes A [
      att "extends" string,
    ] Opts,
    (Opts =!=> register).
  main Args :-
    coq.error "Called with wrong arguments:" Args _.
}}. *)
