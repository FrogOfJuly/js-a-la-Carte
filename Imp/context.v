From Stdlib Require Import Structures.Orders.
From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.Decidable.
Set Implicit Arguments.

Module Type STRING.

 Parameter string : Set.
 Declare Module String_as_OT : UsualOrderedType with Definition t := string.
 Declare Module Ordered : Structures.OrderedType.OrderedType
   with Definition t := string.
 Module OrderedTypeFacts := Structures.OrderedType.OrderedTypeFacts (Ordered).
 Parameter string_eq_dec : forall s1 s2 : string, {s1 = s2} + {~ s1 = s2}.
 Parameter string_dec_eq : forall s1 s2 : string, s1 = s2 \/ ~ s1 = s2.

End STRING.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.
  Declare Module Ordered : Structures.OrderedType.OrderedType 
    with Definition t := atom.
  Module OrderedTypeFacts := Structures.OrderedType.OrderedTypeFacts (Ordered).
  Parameter atom_fresh_for_list : forall (xs : list atom), 
    exists x : atom, ~ List.In x xs.
  Parameter atom_eq_dec : forall a1 a2 : atom, {a1 = a2} + {~ a1 = a2}.
  Parameter atom_dec_eq : forall a1 a2 : atom, a1 = a2 \/ ~ a1 = a2.

End ATOM.

From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import FSets.FMapList.
From Stdlib Require Import Strings.String.
Require Import Datatypes.
Set Implicit Arguments.

Module Env (Import Atom : ATOM) (Import String : STRING).

Module AtomEnv := FSets.FMapList.Make (Atom.Ordered).

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.

Parameter __proto__ : string.

End Env.
