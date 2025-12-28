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
    std.filter DepRepMatched (x\ x = (pr _N [])) [], !, 
    std.map DepRepMatched extract DepRepMatched',
    std.map DepRepMatched' (x\ r\ r is (global x)) DepRepMatched'',
    coq.say "> Ided deps:" DepRepMatched'',
    Res = app ((global GRef)::DepRepMatched''),
    std.assert-ok! (coq.typecheck Res Ty) "generated term failed to typecheck",
    coq.say Res,
    refine Res G GL.

  pred extract' i:goal-ctx i:(pair string (list prop)) o:term.
  extract' _ P R :-
    P = pr N L,
    coq.say "Found these" P,
    std.mem L (represented_as R' N), !,
    R is (global R').
  extract' Ctx P R :-
    P = pr N [],
    coq.say "Found these" P,
    coq.string->name N N',
    coq.say "Ctx:" Ctx,
    % TODO: coq.name->id is for internal usage
    std.filter Ctx (x\ x = decl _ Nn _, coq.name->id Nn N) Ctx',
    coq.say "Ctx':" Ctx',
    std.mem Ctx' (decl H _ Ty),
    coq.say "found in ctx:" H  N' ":" Ty,
    R is H.

  solve (goal Ctx A TyG B [str IndName] as _G) GL :-
    coq.say "Found thing:" IndName,
    std.assert! (coq.locate IndName GRef) "can't locate",
    solve (goal Ctx A TyG B [trm (global GRef)]) GL.

  solve (goal Ctx _ TyG _ [trm (global GRef)] as G) GL :-
    coq.say "> Found gref:" GRef,
    % Resolve from databases
    resolve_dependencies GRef DepRepMatched,
    % Resolve from goal context
    std.filter DepRepMatched (x\ (x = (pr N []), coq.say "Can't resolve" N)) DepRepUnresolved, !,
    coq.say "> Unresolved deps:" DepRepUnresolved,
    std.map DepRepMatched (x\ r\ extract' Ctx x r) DepRepMatched',
    coq.say "> Meee deps:" DepRepMatched',
    Res = app ((global GRef)::DepRepMatched'),
    std.assert-ok! (coq.typecheck Res Ty) "generated term failed to typecheck",
    coq.say "resulting term:" Res ":" Ty "while goal is" TyG,
    refine Res G GL.

  solve Args G :- 
    coq.say "What do" Args ", G:" G,
    coq.ltac.fail 0 "Do not know what to do".
}}.


Elpi Db section_template.db lp:{{
  pred is_section_template i:string.

  :name "is_section_template.fail"
  is_section_template Name :- coq.error "I don't know this section tempalte:" Name.

  pred section_vars i:string o:list (pair string string).

  :name "section_vars.fail"
  section_vars Name _ :- coq.error "I don't know this section tempalte:" Name.
}}.



Elpi Command print_all_section_vars.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{

  :before "is_section_template.fail"
  is_section_template _ :- !, fail. % softly

  :before "section_vars.fail"
  section_vars _ _ :- !, fail. % softly

  main [] :-
    std.findall (is_section_template _) Rules1,
    std.findall (section_vars _ _) Rules2,

    std.forall Rules1 print-rule,
    std.forall Rules2 print-rule.

  pred print-rule i:prop.
  print-rule (is_section_template P) :- coq.say "section" P.
  print-rule (section_vars P N) :- coq.say "Variables" P N.

}}.

Elpi Command SectionTemplate.
#[synterp] Elpi Accumulate lp:{{ 
  main [str "Section", str SectionName]
  :-  coq.say "synterop: Found section template:" SectionName
    , coq.env.begin-section SectionName
    .
  main [str SectionName]
  :-  coq.say "synterop: middle" SectionName
    % , coq.env.end-section
    .
  
  main [str "End", str SectionName]
  :-  coq.say "synterop: Ending section template:" SectionName
    , coq.env.end-section
    .
}}.
Elpi Accumulate Db section_template.db.
Elpi Accumulate lp:{{ 

  :name "is_section_template.soft_fail"
  :before "is_section_template.fail"
  is_section_template _ :- !, fail. % softly

  :name "section_vars.soft_fail"
  :before "section_vars.fail"
  section_vars _ _ :- !, fail. % softly
  
  main [str "Section", str SectionName]
  :-  coq.say "Found section template:" SectionName
    , if (is_section_template SectionName) (coq.error "Template with this name exists:" SectionName) true
    , TheNewRule = is_section_template SectionName
    , coq.env.begin-section SectionName
    , coq.elpi.accumulate _ "section_template.db" (clause _ (before "is_section_template.fail") TheNewRule)
    , coq.say "Printing:"
    , coq.say "Added new template" SectionName
    .
  main [str SectionName] 
  :-  coq.say "middle"
    , coq.env.section Variables
    , std.map Variables (x\ r\ coq.typecheck (global (const x)) Ty ok, std.any->string Ty r) VariableTys
    , std.map Variables (x\ r\ r is {std.any->string x}) Variables'
    , std.zip Variables' VariableTys R
    , coq.say "Variables:" R
    , TheNewRule = section_vars SectionName R
    , coq.elpi.accumulate _ "section_template.db" (clause _ (before "section_vars.fail") TheNewRule)
    , coq.say "Accumulated"
    .
  main [str "End", str SectionName]
  :-  coq.say "Ending section template:" SectionName
    , coq.env.current-section-path SecPath
    , if (std.rev SecPath (SectionName::_)) true (coq.error "Trying to close mismatching section:" SectionName "Current section path:" SecPath)
    , if (is_section_template SectionName)  true (coq.error "Trying to close section that does not exist:" SectionName) 
    , coq.env.end-section
    .
  main Args 
  :-  coq.say "What do: " Args
    .
}}.

Elpi Command What.
Elpi Accumulate lp:{{ 
pred section_vars i:string o:list (pair string string).

main [str SectionName] 
  :- coq.say "middle"
   , coq.env.section Variables
   , std.map Variables (x\ r\ coq.typecheck (global (const x)) Ty ok, std.any->string Ty r) VariableTys
   , std.map Variables (x\ r\ r is {std.any->string x}) Variables'
   , std.zip Variables' VariableTys R
   , coq.say "Variables:" R
   , TheNewRule = section_vars SectionName R
   , coq.elpi.accumulate _ "section_template.db" (clause _ (before "section_vars.fail") TheNewRule)
   , coq.say "Accumulated"
  .
}}.

Elpi SectionTemplate
Section exp_lam'.

    Variable exp : Type.
    
    Inductive exp_lam : Type := 
        | ab : exp -> exp_lam
        | app : exp -> exp -> exp_lam
        | bvar : nat -> exp_lam
    .

Elpi What "exp_lam'".

Elpi print_all_section_vars.

Elpi SectionTemplate
End exp_lam'.

(* End exp_lam'. *)

