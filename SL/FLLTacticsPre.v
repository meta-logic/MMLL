(** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export MMLL.Misc.Utils.
Require Export MMLL.SL.Sequent.
Require Import MMLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section MMLL. *)

(** Solves some efficiency problems related to rewriting with setoids *)
(* Remove Hints Equivalence.pointwise_equivalence : typeclass_instances. *)
Existing Instance Equivalence.pointwise_equivalence | 11.

Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform_oo _] =>  constructor 
    | [|- uniform _ ] => eauto 10  using uniform_id, uniform_con, uniform_app, proper_uniform, abstr_lambda
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.



Ltac simplF := 
 repeat    
  match goal with
  | [ |- subexp ] => exact loc
  | [ |- SetU (getU _) ] => apply getUtoSetU
  | [ |- SetU (Loc _) ] => apply SetULoc  
  | [ |- SetT (Loc _) ] => apply SetTLoc    
  | [ |- SetL (getL _) ] => apply getLtoSetL
    
  | [  |- context[length []] ] => simpl
  | [ H: context[length []]  |- _ ] => simpl in H
  | [  |- context[Loc []] ] => simpl
  | [ H:  context[Loc []] |- _ ] => simpl in H
  | [  |- context[PlusT []] ] => simpl
  | [ H:  context[PlusT []] |- _ ] => simpl in H
  | [  |- context[second []] ] => simpl
  | [ H:  context[second []] |- _ ] => simpl in H
 
 | [  |- context[Loc(_++_)] ] => setoid_rewrite locApp
 | [  |- context[getU(_++_)] ] => setoid_rewrite getUApp
 | [  |- context[getL(_++_)] ] => setoid_rewrite getLApp
 | [  |- context[getU(getU _)] ] => rewrite getU_fixpoint
 | [  |- context[getL(getL _)] ] => rewrite getL_fixpoint
 | [  |- context[PlusT (PlusT _)] ] => rewrite PlusT_fixpoint 
 | [  |- context[getU(getL _)] ] => rewrite getUgetL
 | [  |- context[getL(getU _)] ] => rewrite getLgetU
 | [  |- context[getU (PlusT (getL _))] ] => rewrite getUgetLPlusT
 | [  |- context[getL (PlusT (getU _))] ] => rewrite getLgetUPlusT
 | [  |- context[getL (Loc _)] ] => rewrite getLELoc 
 | [  |- context[getU (PlusT (getU _))] ] => rewrite getUPlusTgetU'
 | [  |- context[getL (Loc _)] ] => rewrite getLELoc

 | [ H: context[Loc(_++_)] |- _ ] => setoid_rewrite locApp in H 
 | [ H: context[getU(_++_)] |- _ ] => setoid_rewrite getUApp in H
 | [ H: context[getL(_++_)] |- _ ] => setoid_rewrite getLApp in H
 | [ H: context[getU(getU _)] |- _ ] => rewrite getU_fixpoint in H
 | [ H: context[getL(getL _)] |- _ ] => rewrite getL_fixpoint in H
 | [ H: context[PlusT (PlusT _)]  |- _ ] => rewrite PlusT_fixpoint in H
 | [ H: context[getU(getL _)] |- _ ] => rewrite getUgetL in H
 | [ H: context[getL(getU _)] |- _ ] => rewrite getLgetU in H
 | [ H: context[getU (PlusT (getL _))]  |- _ ] => rewrite getUgetLPlusT in H
 | [ H: context[getL (PlusT (getU _))]  |- _ ] => rewrite getLgetUPlusT in H  
 | [ H: context[getL (Loc _)]  |- _ ] => rewrite getLELoc in H  
 | [ H: context[getU (PlusT (getU _))]  |- _ ] => rewrite getUPlusTgetU' in H  
 | [ H: context[getL (Loc _)] |- _  ] => rewrite getLELoc in H

 | [ H: context[Loc ((_,_)::_)] |- _ ] => simpl in H
 | [ H: context[getU((_,_)::_)] |- _ ] => simpl in H
 | [ H: context[getL((_,_)::_)] |- _ ] => simpl in H
 | [ |- context[getU((_,_)::_)] ] => simpl
 | [ |- context[getL((_,_)::_)] ] => simpl
 
 | [ H: context[if u loc then _ else _] |- _ ] => rewrite locu in H
 | [ H: context[if mt loc then _ else _] |- _ ] => rewrite locT in H
 | [ H: context[if md loc then _ else _] |- _ ] => rewrite locD in H
 | [ H: context[if m4 loc then _ else _] |- _ ] => rewrite loc4 in H
 | [ H: context[if mk loc then _ else _] |- _ ] => rewrite locK in H
 | [ |- context[if u loc then _ else _]  ] => rewrite locu 
 | [ |- context[if mt loc then _ else _] ] => rewrite locT 
 | [ |- context[if md loc then _ else _] ] => rewrite locD 
 | [ |- context[if m4 loc then _ else _] ] => rewrite loc4 
 | [ |- context[if mk loc then _ else _] ] => rewrite locK 
 
  | [ H1: u (fst ?F) = _, H2: context[getU (?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; rewrite H1 in H2 
  | [ H1: u (fst ?F) = _, H2: context[getL (?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; rewrite H1 in H2      
  | [ H: u (fst ?F) = true |- context[getU (?F :: _)] ] => 
     destruct F;simpl;simpl in H; rewrite H 
  | [ H: u (fst ?F) = true |- context[getL (?F :: _)] ] => 
     destruct F;simpl;simpl in H; rewrite H 

 | [ H1: ?s ?a = _, H2: context[if ?s ?a then _ else _] |- _ ] => rewrite H1 in H2 
 | [ H: ?s ?a = _|- context[if ?s ?a then _ else _] ] => rewrite H 

 | [ H1: u ?i = false, H2: In (?i, ?F) ?B  |- In (?i, ?F) (getL ?B) ] => apply lIngetL
 | [ H: SetK4 ?i ?K  |- SetK4 ?i (getU ?K) ] => apply SetK4Destruct in H
 | [ H: SetK4 ?i ?K  |- SetK4 ?i (getL ?K) ] => apply SetK4Destruct in H
 | [ H: SetK ?i ?K  |- SetK ?i (getU ?K) ] => apply SetKDestruct in H 
 | [ H: SetK ?i ?K  |- SetK ?i (getL ?K) ] => apply SetKDestruct in H 

 | [ H1: u ?i = true, H2: SetK ?i ?K  |- SetU ?K  ] => eapply (SetUKClosure H1);simplF
 | [ H1: mt ?i = true, H2: SetK ?i ?K  |- SetT ?K  ] => eapply (SetTKClosure H1);simplF 
 | [ H1: u ?i = true, H2: SetK4 ?i ?K  |- SetU ?K  ] => eapply (SetUK4Closure H1);simplF
 | [ H1: mt ?i = true, H2: SetK4 ?i ?K  |- SetT ?K  ] => eapply (SetTK4Closure H1);simplF 

 | [ H1: u ?i = true, H2: SetK ?i ?K  |- SetU (_ ?K)  ] => eapply (SetUKClosure H1);simplF
 | [ H1: mt ?i = true, H2: SetK ?i ?K  |- SetT (_ ?K)  ] => eapply (SetTKClosure H1);simplF 
 | [ H1: u ?i = true, H2: SetK4 ?i ?K  |- SetU (_ ?K)  ] => eapply (SetUK4Closure H1);simplF
 | [ H1: mt ?i = true, H2: SetK4 ?i ?K  |- SetT (_ ?K)  ] => eapply (SetTK4Closure H1);simplF 

end.

   
Ltac cleanF :=
 repeat
 match goal with
 | [H: release top  |- _] => clear H
 | [H: release bot  |- _] => clear H
 | [H: release (MOr _ _)  |- _] => clear H
 | [H: release (atom _)  |- _] => clear H
 | [H: release (All _)  |- _] => clear H
 | [H: release (AAnd _ _)  |- _] => clear H
 | [H: release (Quest _ _)  |- _] => clear H
 
 | [H: asynchronous top  |- _] => clear H
 | [H: asynchronous bot  |- _] => clear H
 | [H: asynchronous (MOr _ _)  |- _] => clear H
 | [H: asynchronous (All _)  |- _] => clear H
 | [H: asynchronous (AAnd _ _)  |- _] => clear H
 | [H: asynchronous (Quest _ _)  |- _] => clear H 
 
 | [H: ~ asynchronous (atom _)  |- _] => clear H
 | [H: ~ asynchronous (perp _)  |- _] => clear H
 | [H: ~ asynchronous zero  |- _] => clear H
 | [H: ~ asynchronous one  |- _] => clear H
 | [H: ~ asynchronous (MAnd _ _)  |- _] => clear H
 | [H: ~ asynchronous (Some _)  |- _] => clear H
 | [H: ~ asynchronous (AOr _ _)  |- _] => clear H
 | [H: ~ asynchronous (Bang _ _)  |- _] => clear H 
 
 | [H : ~ IsPositiveAtom (perp _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MOr _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MAnd _ _) |- _ ] => clear H   
 | [H : ~ IsPositiveAtom (AAnd _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (AOr _ _) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Bang _ _) |- _ ] => clear H    
 | [H : ~ IsPositiveAtom (Quest _ _) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (All _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Some _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom top |- _ ] => clear H    
 | [H : ~ IsPositiveAtom bot |- _ ] => clear H 
 | [H : ~ IsPositiveAtom one |- _ ] => clear H 
 | [H : ~ IsPositiveAtom zero |- _ ] => clear H  
    
    | [H : SetK _ [] |- _ ] => clear H
    | [H : SetK4 _ [] |- _ ] => clear H
    | [H : SetT [] |- _ ] => clear H
    | [H : SetU [] |- _ ] => clear H
    | [H : SetL [] |- _ ] => clear H   
 end.
 
(** This tactic solves most of the irrelevant goals in a focused
  proof (e.g., proving whether a formula is positive or not) *)
Ltac solveF :=
  simpl;auto;subst;
  let H := fresh "H" in
  repeat
    match goal with
  | [ H: SetU ?L |- Permutation (getL ?L) (getL ?L ++ getL ?L) ] => 
    rewrite (SetU_then_empty H);simpl;auto
  
   | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = true ] => apply locK 
  | [ |- md loc = false ] => apply locD
    
  | [ |- subexp ] => exact loc
    
  | [H: u loc = false |- _] => rewrite locu in H; discriminate H   
  | [H: mk loc = false |- _] => rewrite locK in H; discriminate H  
  | [H: mt loc = false |- _] => rewrite locT in H; discriminate H  
  | [H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H  
  | [H: md loc = true |- _] => rewrite locD in H; discriminate H  

   
  | [H1: ?a <> loc, H2: lt ?a loc |- _] => apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
| [H1: ?a <> loc, H2: lt loc ?a |- _] => apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction

    | [ |- uniform _ ] => solve [solveUniform]
    | [ |- _ <= _ ] => lia
    | [ |- _ >= _ ] => lia
    | [ |- _ < _ ] => lia
    | [ |- _ > _ ] => lia                       
    | [|- ~ asynchronous _] => first [solve [intro H; inversion H;auto] | auto] 
    | [|- ~ IsPositiveAtom _ ] => first [solve [intro H; inversion H;auto] | auto] 
    | [|- IsPositiveAtom _ ] => repeat constructor
    | [|- release _] => first [solve [constructor] | auto]  
(*     | [|- Remove _ _ _] => constructor
    | [H: Remove _ [?F] ?L |- _] =>  apply RemoveUnique in H;subst
 *)    | [|- asynchronous _] => first [solve [constructor] | auto]

    | [H: release ?F  |- _] =>
      match F with
      | MAnd _ _ => inversion H
      | perp _ => inversion H
      | Some _ => inversion H
      | zero => inversion H
      | one => inversion H
      | AOr _ _ => inversion H
      | Bang _ _ => inversion H
      end
    | [H : ~ asynchronous ?F |- _ ] =>
      match F with
      | AAnd _ _ => contradict H;constructor
      | MOr _ _ => contradict H;constructor
      | All _ => contradict H;constructor
      | Quest _ _ => contradict H;constructor
      | Bot => contradict H;constructor
      | Top => contradict H;constructor
      end
    | [H : ~ IsPositiveAtom (atom _ ) |- _ ] => contradict H;constructor
    | [H: (atom _ ) = (atom _ ) |- _ ] => inversion H;clear H
    | [H: seqN _ _ _ _  (>> zero) |- _ ] => inversion H;solveF
    | [H: seq  _ _ _  (>> zero) |- _ ] => inversion H;solveF
    | [ |- _ >= _] => subst; lia
    | [ |- _ <= _] => subst; lia
    end;auto;
  try(match goal with
      | [ |- Permutation _ _] =>  simplF; perm
      end).

(** Splits the linear context L into L1 ++ L2 where L1 contains the first n elements of L *)
Ltac SplitContext n :=
  match goal with
  | [ |- seqN _ _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.

Ltac SplitContext' n :=
  match goal with
  | [ |- seq _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.



Tactic Notation "store" := match goal with
                           | [ |- seq _ _ _ _ ] =>  apply tri_store' ;solveF
                           | [|- seqN _ _ _ _ _] => apply tri_store ;solveF
                           end.

Tactic Notation "par" := match goal with
                         | [ |- seq _ _ _ _ ] =>  apply tri_par' ;solveF
                         | [|- seqN _ _ _ _ _] => apply tri_par ;solveF
                         end.

Tactic Notation "release" := match goal with
                         | [ |- seq _ _ _ _ ] =>  apply tri_rel' ;solveF
                         | [|- seqN _ _ _ _ _] => apply tri_rel ;solveF
                         end.

  
Tactic Notation "init1"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_init1';try solveSet;auto
                          | [|- seqN _ _ _ _ _] => apply tri_init1;try solveSet;auto
                          end.


Tactic Notation "init2" constr(a) constr(b) := match goal with
                          | [ |- seq _ _ _ _ ] =>  eapply @tri_init2' with (i:=a) (C:=b);[try solveSet | auto | try perm ];auto
                          | [|- seqN _ _ _ _ _] => eapply @tri_init2 with (i:=a) (C:=b);[try solveSet | auto | try perm ];auto
                          end.

Tactic Notation "init2" constr(a) := match goal with
                          | [ |- seq _ _ _ _ ] =>  eapply @tri_init2' with (i:=a) 
                          | [|- seqN _ _ _ _ _] => eapply @tri_init2 with (i:=a) 
                          end.
                          
Tactic Notation "init2" := match goal with
                          | [ |- seq _ _ _ _ ] =>  eapply @tri_init2'
                          | [|- seqN _ _ _ _ _] => eapply @tri_init2
                          end.

                          
                          
(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)


  
Ltac solvell :=
  try
    match goal with
    (* initial Rules *)
    | [ |- seqN _ _ _ [atom ?A] (>> (perp ?A))] => init1
  
    | [ |- seqN _ _ ((?i,atom ?A)::?B) [] (>> (perp ?A))] => init2 i B
    | [ |- seqN _ _ (?B++[(?i,atom ?A)]) [] (>> (perp ?A))] => init2 i B
    | [ |- seqN _ _ (?X::?B++[(?i,atom ?A)]) [] (>> (perp ?A))] => init2 i (X::B)
    | [ |- seqN _ _ (?B++(?i,atom ?A)::?E) [] (>> (perp ?A))] => init2 i (B++E)    
    | [ |- seqN _ _ (?X::?B++(?i,atom ?A)::?E) [] (>> (perp ?A))] => init2 i (X::B++E)       
    | [ H: Permutation ((?i,atom ?A)::?B) ?D |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation (?B++[(?i,atom ?A)]) ?D |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation (?B++(?i,atom ?A)::?E) ?D |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i (B++E)

    | [ H: Permutation ?D ((?i,atom ?A)::?B)  |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation ?D (?B++[(?i,atom ?A)])  |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation ?D (?B++(?i,atom ?A)::?E)  |- seqN _ _ ?D [] (>> (perp ?A))] => init2 i (B++E)

    
    | [H: seqN _ _ _ _ (>> zero) |- _ ] => inversion H;subst;solveF
          
    | [|- seqN _ _ _ [] (>>  One)] => apply tri_one;try solveSet;auto
    | [H: tri_bangK4 _ 0 _ _ _ _ _ |- _ ] => inversion H 
    
    | [H: seqN _ 0 _ _ (> AAnd _ _::?L) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (> Bot ::?L) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (> MOr _ _::?L) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (> All _ ::?L) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (> atom _::?L) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (> perp _::?L) |- _ ] => inversion H 
    
    | [H: seqN _ 0 _ _ (> Quest _ _::?L) |- _ ] => inversion H 
    
    | [H: seqN _ 0 _ _ (>> (MAnd _ _)) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (>> (AOr _ _)) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (>> (Bang _ _)) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (>> (Some _)) |- _ ] => inversion H 
    | [H: seqN _ 0 _ _ (>> (atom _)) |- _ ] => inversion H 
    
   
    (* Change of polarity *)
    | [H: release ?F |- seqN _ _ _ _ (>>  ?F)] => release;solvell
    | [|- seqN _ _ _ _ (>>  ?F)] =>
      match F with
      | MOr _ _ => release;solvell
      | All _ =>release;solvell
      | Bot  => release;solvell
      | (atom _)  => release;solvell
      | Top  => release;solvell
      | AAnd _ _  => release;solvell
      | Quest _ _ => release;solvell
      | Bang loc _ => apply tri_bangL;try solveSet;solvell
      | Bang _ _ => apply tri_bang;solvell
      end
    (* Negative Phase *)
    | [ H: ~ asynchronous ?F |- seqN _ _ _ _ (> (?F:: _ ))] => store;auto;solvell
    | [ |- seqN _ _ _ _ (> ((One ) :: _ ))] => store ;solvell
    | [ |- seqN _ _ _ _ (> ((Zero ) :: _ ))] => store ;solvell
    | [ |- seqN _ _ _ _ (> ((atom _ ) :: _ ))] => store ;solvell
    | [ |- seqN _ _ _ _ (> ((perp _ ) :: _ ))] => store ;solvell
    | [ |- seqN _ _ _ _ (> ( (Bang _ _) :: _)) ] => store ;solvell
    | [ |- seqN _ _ _ _ (> ( (Quest _ _) :: _)) ] => apply tri_quest ;solvell
    | [ |- seqN _ _ _ _ (> ( (Top) :: _))  ] => apply tri_top
    | [ |- seqN _ _ _ _ (> ( (MOr _ _) :: _)) ] => par ;solvell
    | [ |- seqN _ _ _ _ (> ( (AOr _ _) :: _)) ] => store ;solvell
    | [ |- seqN _ _ _ _ (> ( (AAnd _ _) :: _)) ] => apply tri_with ;solvell
    | [ |- seqN _ _ _ _ (> ( (Bot) :: _)) ] => apply tri_bot ;solvell
    | [ |- seqN _ _ _ _ (> ( (MAnd _ _) :: _)) ] => store ;solvell
    | [ |- seqN _ _ _ _ (> ( (All _) :: _)) ] => let x:= fresh "x" in
                                                 let xp := fresh "properX" in
                                                 apply tri_fx ;try solveUniform; intros x xp ; solvell
    | [ |- seqN _ _ _ _ (> ((Some _ ) :: _ ))] => store ;solvell
    end.
  
  
Lemma init2Cut (OLS : OLSig) (SI:Signature) i A L th :
SetU L -> mt i = true ->
In (i,atom A) L -> seq th L [] (>> perp A).
 Proof .
 intros. 
 apply InPermutation in H1;sauto...
 rewrite H1 in H. 
 init2 i x.
 Qed.
  
Ltac solvell' :=
  try
    match goal with
    (* initial Rules *)
    | [ |- seq _ _ [atom ?A] (>> (perp ?A))] => init1
    
    | [ H: SetU ?L, Hm: mt ?i = true, HIn: In (?i,atom ?A) ?L |- seq _ ?L [] (>> (perp ?A))] =>  try solve [refine (init2Cut i _ _ _ _ _);auto]
   
    | [ |- seq _ ((?i,atom ?A)::?B) [] (>> (perp ?A))] => init2 i B
    | [ |- seq _ (?B++[(?i,atom ?A)]) [] (>> (perp ?A))] => init2 i B
    | [ |- seq _ (?X::?B++[(?i,atom ?A)]) [] (>> (perp ?A))] => init2 i (X::B)
    | [ |- seq _ (?B++(?i,atom ?A)::?E) [] (>> (perp ?A))] => init2 i (B++E)   
    | [ |- seq _ (?X::?B++(?i,atom ?A)::?E) [] (>> (perp ?A))] => init2 i (X::B++E)   
    
    | [ H: Permutation ((?i,atom _)::?B) ?D |- seq  _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation (?B++[(?i,atom ?A)]) ?D |- seq _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation (?B++(?i,atom ?A)::?E) ?D |- seq _ ?D [] (>> (perp ?A))] => init2 i (B++E)

    | [ H: Permutation ?D ((?i,atom ?A)::?B)  |- seq _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation ?D (?B++[(?i,atom ?A)])  |- seq _ ?D [] (>> (perp ?A))] => init2 i B
    | [ H: Permutation ?D (?B++(?i,atom ?A)::?E)  |- seq _ ?D [] (>> (perp ?A))] => init2 i (B++E)

    | [H: seq _ _ _ (>> zero) |- _ ] => inversion H;subst;solveF
    
    | [|- seq _ _ [] (>>  One)] => apply tri_one';try solveSet;auto
    | [|- seq _ _ [] (>>  MAnd _ _)] => apply tri_tensor' with (M:=[]) (N:=[]); [perm|solvell'|solvell'] (* tensor with the empty context *)
     (* Change of polarity *)
    | [H: release ?F |- seq _ _ _ (>>  ?F)] => release;solvell'
    | [|- seq _ _ _ (>>  ?F)] =>
      match F with
      | MOr _ _ => release;solvell'
      | All _ =>release;solvell'
      | Bot  => release;solvell'
      | (atom _)  => release;solvell'
      | Top  => release;solvell'
      | AAnd _ _  => release;solvell'
      | Quest _ _ => release;solvell'
      | Bang loc _ => apply tri_bangL';try solveSet;solvell'
      | Bang _ _ => apply tri_bang';solvell'
      end
    (* Negative Phase *)
    | [ H: ~ asynchronous ?F |- seq _ _ _ (> (?F:: _ ))] => store;auto;solvell'
    | [ |- seq _ _ _ (> ((One) :: _ ))] => store ;solvell'
    | [ |- seq _ _ _ (> ((Zero) :: _ ))] => store ;solvell'
    | [ |- seq _ _ _ (> ((atom _ ) :: _ ))] => store ;solvell'
    | [ |- seq _ _ _ (> ((perp _ ) :: _ ))] => store ;solvell'
    | [ |- seq _ _ _ (> ((Bang _ _) :: _ ))] => store ;solvell'
    | [ |- seq _ _ _ (> ( (Quest _ _) :: _)) ] => apply tri_quest' ;solvell'
    | [ |- seq _ _ _ (> ( (Top) :: _))  ] => apply tri_top'
    | [ |- seq _ _ _ (> ( (MOr _ _) :: _)) ] => par ;solvell'
    | [ |- seq _ _ _ (> ( (AOr _ _) :: _)) ] => store ;solvell'
    | [ |- seq _ _ _ (> ( (AAnd _ _) :: _)) ] => apply tri_with' ;solvell'
    | [ |- seq _ _ _ (> ( (Bot) :: _)) ] => apply tri_bot' ;solvell'
    | [ |- seq _ _ _ (> ( (MAnd _ _) :: _)) ] => store ;solvell'
    | [ |- seq _ _ _ (> ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp  ;solvell'
    | [ |- seq _ _ _ (> ((Some _ ) :: _ ))] => store ;solvell'
    end.

Ltac solveLL :=
   match goal with
   | [ |- seq _ _ _ _ ] =>  solvell'
   | [|- seqN _ _ _ _ _] => solvell
   | _ => solveF
   end;auto.
  
(*
(** Decision rule on the linear context based on the position of the formula *) 
Ltac dec1' n :=
  ExchangeFront' n;
  match goal with
    [|- seq _ _ (?G :: _) (> []) ] =>
    eapply tri_dec1' with (F:= G);solveF
  end.
(** Decision rule on the linear context based on the position of the formula *) 
Ltac dec1 n :=
  ExchangeFront n;
  match goal with
    [|- seqN _ _ _ (?G :: _) (> []) ] =>
    eapply tri_dec1 with (F:= G);solveF
  end.
*)




(** Notation for forward reasoning on FLL sequents *)
Tactic Notation "decide1"  constr(R) := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R);solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R);solveF;solveLL 
                                        end;solveF.

Tactic Notation "decide1"  constr(R) constr(T) := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R) (L':=T);solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R) (L':=T);solveF;solveLL 
                                        end;solveF.
                                        
                                        

Tactic Notation "decide2l"  constr(R) constr(S)  constr(T) := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:= R) (B':= T);solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec2l with (F:= S)(i:= R) (B':= T);solveF;solveLL
                                        end;solveF.
  
 Tactic Notation "decide2l"  constr(R) constr(S)   := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:= R) ;solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec2l with (F:= S)(i:= R) ;solveF;solveLL
                                        end;solveF.
                                        
   
                                                                                
Tactic Notation "decide2u"  constr(R) constr(S) := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2u' with (F:= S) (i:= R);solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec2u with (F:= S)(i:= R);solveF;solveLL
                                        end;solveF.
                                        
                                        
Tactic Notation "decide3"  constr(R) := match goal with
                                        | [ |- seq _ _ _ _ ] =>  eapply @tri_dec3' with (F:= R);solveF;solveLL
                                        | [|- seqN _ _ _ _ _] => eapply @tri_dec3 with (F:= R);solveF;solveLL
                                        end;solveF.

Tactic Notation "tensor"  constr(Ctx1) constr(Ctx2) constr(Ctx3) constr(Ctx4) := match goal with
                                                       | [ |- seq _ _ _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (D:=Ctx4);solveF;solveLL
                                                       | [|- seqN _ _ _ _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (D:=Ctx4);solveF;solveLL
                                                       end.

Tactic Notation "tensor"  constr(Ctx1) constr(Ctx2) := match goal with
               | [ |- seq _ ?C _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=C) (D:=C);solveF;solveLL
               | [|- seqN _ _ ?C _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=C) (D:=C);solveF;solveLL
                 end.

Tactic Notation "tensor"  := match goal with
               | [ |- seq _ ?C [] _ ] =>  eapply @tri_tensor' with (M:=nil) (N:=nil) (B:=C) (D:=C);solveF;solveLL
               | [|- seqN _ _ ?C [] _] => eapply @tri_tensor with (M:=nil) (N:=nil) (B:=C) (D:=C);solveF;solveLL
                 end.

Tactic Notation "copyK4"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _ ] => eapply @tri_copyK4' with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyK4 with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       end.
                                                      
Tactic Notation "copyUK"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyUK' with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyUK with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       end. 
                                                       
Tactic Notation "copyLK"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyLK' with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyLK with (b:=i) (F:=P) (B':=B);try solveSet;solveF;solveLL
                                                       end.   
                                                                                                            
   
Tactic Notation "finishExp"  := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_exp';solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_exp;solveF;solveLL
                                                       end. 
                                                                                                           
Tactic Notation "oplus1" := match goal with
                           | [ |- seq _ _ _ _ ] =>   apply tri_plus1';solveLL
                           | [|- seqN _ _ _ _ _] =>  apply tri_plus1;solveLL
                            end.

Tactic Notation "oplus2" := match goal with
                           | [ |- seq _ _ _ _ ] =>   apply tri_plus2';solveLL
                           | [|- seqN _ _ _ _ _] =>  apply tri_plus2;solveLL
                            end.



Tactic Notation "existential" constr(tt) := match goal with
                                            | [ |- seq _ _ _ _ ] => eapply @tri_ex' with (t:=tt);try solveUniform ; auto;solveLL 
                                            | [|- seqN _ _ _ _ _] => eapply @tri_ex with (t:=tt);try solveUniform; auto;solveLL
                                            end.

Tactic Notation "foraLL" := match goal with
                                | [ |- seq _ _ _ _ ] => eapply @tri_fx'; intros; auto
                                | [|- seqN _ _ _ _ _] => eapply @tri_fx; intros; auto
                                end.

Tactic Notation "createWorld" constr(a) := match goal with
                | [ |- seq _ _ _ _ ] => eapply @tri_bangD' with (i:=a); try solve [intro ;subst;solveSubExp];auto
                | [|- seqN _ _ _ _ _] => eapply @tri_bangD with (i:=a);try solve [intro ;subst;solveSubExp];auto
                                end.

Tactic Notation "createWorld" := match goal with
                | [ |- seq _ _ _ _ ] => eapply @tri_bang';auto
                | [|- seqN _ _ _ _ _] => eapply @tri_bang;auto
                end.
                 
     Lemma asas (OLS: OLSig) (SI: Signature) th a C F G : seq th C [] (>> a ! F ** G).
     createWorld.
     Abort. 


             
(** Given a rule R (belonging to the theory), this rule introduces R
  (using [tri_dec3]) and then tries to decompose such formula using
  [solveLL]. 
Ltac bipole Rule :=
  match goal with
  | [|- seqN _ _ _ (?A :: ?L) (> [] ) ] =>
    decide3 Rule;
    tensor [A] L; solveLL
  end.
Ltac bipole' Rule :=
  match goal with
  | [|- seq _ _ (?A :: ?L) (> [] ) ] =>
    decide3 Rule;
    tensor [A] L; solveLL
  end.
*)

(** Erasing some of the (unimportant) hypotheses added by the [solveF] and [solveLL] procedures *)

Ltac CleanContext :=
  sauto;simplF;cleanF;solveF.

