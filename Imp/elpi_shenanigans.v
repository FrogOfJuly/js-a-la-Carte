From elpi Require Import elpi.



Elpi Db section_deps.db lp:{{

  % A typical Db is made of one main predicate
  pred section_deps o:gref, o: list gref.

  % the Db is empty for now, we put a rule giving a
  % descriptive error and we name that rule "age.fail".
  :name "section_deps.fail"
  section_deps GRef _ :- coq.error "I don't know what" GRef "is!".

  pred represents o:gref, o:string.

  :name "represents.fail"
  represents GRef _ :- coq.error "I don't know what" GRef "represents!".

  pred section_deps_repr o:gref, o: list string.

  :name "section_deps_repr.fail"
  section_deps_repr GRef _ :- coq.error "I don't know what representations" GRef "depends on!".

  pred represented_as o:gref, o:string.

  :name "represented_as.fail"
  represented_as GRef _ :- coq.error "I don't know what" GRef "is represented as!".
}}.

Elpi Command SetSectionDeps.
Elpi Accumulate Db section_deps.db.
Elpi Accumulate lp:{{
  main [trm (global GRef)] :-
    coq.env.transitive-dependencies GRef _ TransDep,
    coq.env.section SectionVarsL,
    std.filter SectionVarsL (x\ coq.gref.set.mem ( const x) TransDep) SectionVarsLRelevant,
    std.map SectionVarsLRelevant (x\ r\ r is const x) SectionVarsLRelevantGref,

    TheNewRule1 = section_deps GRef SectionVarsLRelevantGref,
    coq.elpi.accumulate _ "section_deps.db"
      (clause _ (before "section_deps.fail") TheNewRule1),

    coq.say "Handling reprs:",

    std.map SectionVarsLRelevantGref (x\ r\ (coq.say x, represents x r)) SectionVarsLRelevantRepr,
    TheNewRule2 = section_deps_repr GRef SectionVarsLRelevantRepr,
    coq.say "Accumulating:" TheNewRule2,
    coq.elpi.accumulate _ "section_deps.db"
      (clause _ (before "section_deps_repr.fail") TheNewRule2).
}}.

Elpi Command print_all_section_deps.
Elpi Accumulate Db section_deps.db.
Elpi Accumulate lp:{{

  :before "section_deps.fail"
  section_deps _ _ :- !, fail. % softly

  :before "represents.fail"
  represents _ _ :- !, fail. % softly

  :before "section_deps_repr.fail"
  section_deps_repr _ _ :- !, fail. % softly

  :before "represented_as.fail"
  represented_as _ _ :- !, fail. % softly

  main [] :-
    std.findall (section_deps _ _) Rules1,
    std.findall (represents _ _) Rules2,
    std.findall (section_deps_repr _ _) Rules3,
    std.findall (represented_as _ _) Rules4,

    std.forall Rules1 print-rule,
    std.forall Rules2 print-rule,
    std.forall Rules3 print-rule,
    std.forall Rules4 print-rule.

  pred print-rule i:prop.
  print-rule (section_deps P N) :- coq.say P "depends on" N.
  print-rule (represents P N) :- coq.say P "represents" N.
  print-rule (section_deps_repr P N) :- coq.say P "depends on repr" N.
  print-rule (represented_as P N) :- coq.say P "is represented as" N.

}}.


Elpi Command RegisterVariable.
Elpi Accumulate lp:{{ 
  pred represents o:gref, o:string.

  main [str "Variable", str VName, str ":", str VTypeName] :-
    % adding variable
    coq.locate-all VTypeName Located,
    std.mem Located (loc-gref TypeGR), 
    coq.env.add-section-variable VName _ (global TypeGR) _, 
    % looking up newly added global reference
    coq.locate VName GRef, !, 
    % bookkeeping
    attributes A,
    coq.parse-attributes A [
      att "represents" string,
    ] Opts,
    (Opts =!=> (
      (get-option "represents" ReprName; ReprName is VName),
      TheNewRule = represents GRef ReprName,
      coq.elpi.accumulate _ "section_deps.db" (clause _ (before "represents.fail") TheNewRule),
      coq.say "RegVar for Any: found variable" VName "with type" TypeGR "representing" ReprName
    )).

  main [str "Variable", str VName, str ":", str "Type"] :-
    % adding variable
    coq.env.add-section-variable VName _ {{ Type }} _,
    % looking up newly added global reference
    coq.locate VName GRef,
    % bookkeeping
    attributes A,
    coq.parse-attributes A [
      att "represents" string,
    ] Opts,
    (Opts =!=> (
      (get-option "represents" ReprName; ReprName is VName),
      TheNewRule = represents GRef ReprName,
      coq.elpi.accumulate _ "section_deps.db" (clause _ (before "represents.fail") TheNewRule), 
      coq.say "RegVar for Type: found variable" VName "with type Type representing" ReprName
    )).
  main [trm (global GRef)] 
   :- coq.say "RegVar: found gref" GRef
    , attributes A
    , coq.parse-attributes A [
        att "represents" string,
      ] Opts
    , (Opts =!=> (
        (get-option "represents" ReprName; ReprName is VName),
        TheNewRule = represents GRef ReprName,
        coq.elpi.accumulate _ "section_deps.db" (clause _ (before "represents.fail") TheNewRule), 
        coq.say "RegVar for Type: found variable" VName "with type Type representing" ReprName
      ))
    .
  main Args :- 
    coq.say "RegVar Failure: What do" Args.
}}.


Section test.
  #[represents = ARepr]
  Elpi RegisterVariable
  Variable A : Type.

  Print A.

  #[represents = xRepr]
  Elpi RegisterVariable
  Variable x : A.

  Print x.  

  
  Variable open_rec : nat -> A -> A -> A.

  #[represents = open_rec]
  Elpi RegisterVariable (open_rec).

  Elpi RegisterVariable
  Variable y : A.

  Definition id := x.

  Definition id' := y.

  Elpi SetSectionDeps (open_rec).

  Elpi SetSectionDeps (id').  

  Elpi SetSectionDeps (id).  

End test.


Elpi Command RegisterRepresented.
Elpi Accumulate lp:{{ 
  pred represented_as o:gref, o:string.

  main [trm (global GRef)] :- 
    attributes A,
    coq.parse-attributes A [
      att "represeted_as" string,
    ] Opts,
    (Opts =!=> (
      (get-option "represeted_as" ReprName; ReprName is VName),
      TheNewRule = represented_as GRef ReprName,
      coq.elpi.accumulate _ "section_deps.db" (clause _ (before "represented_as.fail") TheNewRule), 
      coq.say "RegisterRepresented:" GRef "is represented as" ReprName
    )).

  main Args :- 
    coq.say "What do:" Args.
}}.

Elpi Tactic specialize_from_section.
Elpi Accumulate Db section_deps.db.
Elpi Accumulate lp:{{ 
  :before "section_deps_repr.fail"
  section_deps_repr _ _ :- !, fail. % softly

  :before "represented_as.fail"
  represented_as _ _ :- !, fail. % softly

  func resolve_dependencies gref -> list (pair string (list prop)).
  resolve_dependencies GRef DepRepMatched :- 
    std.findall (section_deps_repr GRef _) DepReps,
    std.mem DepReps (section_deps_repr _ DepRepList), !, 
    coq.say "> Found gref deps:" DepRepList,
    std.map DepRepList 
      (x\ r\ std.findall (represented_as _ x) r
      ) DepRepListResolved,
    coq.say "> Resolved deps:" DepRepListResolved,
    std.zip DepRepList DepRepListResolved DepRepMatched,
    coq.say "> Matched deps:" DepRepMatched.

  func extract (pair string (list prop)) -> gref.
  extract P R :-
    coq.say "Found these" P,
    P = pr N L,
    std.mem L (represented_as R N), !.


  solve (goal _ _ Ty _ [str IndName] as G) GL :-
    coq.say "Found thing:" IndName,
    std.assert! (coq.locate IndName GRef) "can't locate",
    coq.say "> Found gref:" GRef,
    resolve_dependencies GRef DepRepMatched,
    std.filter DepRepMatched (x\ x = (pr _N []), coq.say "Goal:" G) [], !, 
    std.map DepRepMatched extract DepRepMatched',
    std.map DepRepMatched' (x\ r\ r is (global x)) DepRepMatched'',
    coq.say "> Ided deps:" DepRepMatched'',
    Res = app ((global GRef)::DepRepMatched''),
    std.assert-ok! (coq.typecheck Res Ty) "generated term failed to typecheck",
    coq.say Res,
    refine Res G GL.

  solve (goal Ctx _ _Ty _ [str IndName] as _G) _GL :-
    coq.say "Found thing:" IndName,
    std.assert! (coq.locate IndName GRef) "can't locate",
    coq.say "> Found gref:" GRef,
    % Resolve from databases
    resolve_dependencies GRef DepRepMatched,
    % Resolve from goal context
    std.filter DepRepMatched (x\ (x = (pr N []), coq.say "Can't resolve" N)) DepRepUnresolved, !,
    coq.say "> Unresolved deps:" DepRepUnresolved,
    coq.ltac.fail 0 "Some section dependencies are missing".

  solve Args G :- 
    coq.say "What do" Args ", G:" G,
    coq.ltac.fail 0 "Do not know what to do".
}}.




Definition foo := 1.


#[represeted_as = y]
Elpi RegisterRepresented (foo).

Definition id_spec := ltac:(elpi specialize_from_section id).

#[represeted_as = ARepr]
Elpi RegisterRepresented (nat).

Elpi Trace Browser.

Definition id_spec := ltac:(elpi specialize_from_section id').

Print id_spec.




Elpi print_all_section_deps.

