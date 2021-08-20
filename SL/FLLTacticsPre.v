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

(* Section FLL. *)

(** Solves some efficiency problems related to rewriting with setoids *)
(* Remove Hints Equivalence.pointwise_equivalence : typeclass_instances. *)
Existing Instance Equivalence.pointwise_equivalence | 11.

Ltac simplSignature := simplSignature1; 
 repeat    
  multimatch goal with
  | [ H: SetU ?K |- context[getL ?K] ] => rewrite (SetU_then_empty H)
  | [ H1: SetU ?K, H2: context[getL ?K] |- _ ] => rewrite (SetU_then_empty H1) in H2
 
 (* About Loc *)
  | [  |- context[Loc(_++_)] ] => setoid_rewrite locApp
  | [  |- context[getL (Loc _)] ] => rewrite getLELoc
  | [  |- context[getU (Loc _)] ] => rewrite getULoc
  | [ H: context[Loc(_++_)] |- _ ] => setoid_rewrite locApp in H 
  | [ H: context[getL (Loc _)] |- _  ] => rewrite getLELoc in H
  | [ H: context[getU (Loc _)] |- _  ] => rewrite getULoc in H

 (* | [ H: SetU ?K |- context[Loc (getU ?K)] ] => rewrite setULocgetU;auto 
 | [ H1: SetU ?K, H2: context[Loc (getU ?K)] |- _ ] => rewrite setULocgetU in H2;auto 
  *) 
 
 (* About PlusT *)
 | [  |- context[PlusT(_++_)] ] => setoid_rewrite PlusTApp
 | [  |- context[PlusT (PlusT _)] ] => rewrite PlusT_fixpoint 
 | [ H1: SetT ?K, H2: context[PlusT ?K] |- _ ] => rewrite SetTPlusT in H2;auto 
 | [ H: SetT ?K |- context[PlusT ?K] ] => rewrite SetTPlusT;auto 
  
 | [ H: context[PlusT(_++_)] |- _ ] => setoid_rewrite PlusTApp in H 
 | [ H: context[PlusT (PlusT _)]  |- _ ] => rewrite PlusT_fixpoint in H
 | [ H: SetU (PlusT _)  |- _ ] => apply PlusTSetU in H

   
 (* About getU and getL *)
 | [  |- context[getU(_++_)] ] => setoid_rewrite getUApp
 | [  |- context[getL(_++_)] ] => setoid_rewrite getLApp
 | [  |- context[getU(getU _)] ] => rewrite getU_fixpoint
 | [  |- context[getL(getL _)] ] => rewrite getL_fixpoint
 | [  |- context[getU(getL _)] ] => rewrite getUgetL
 | [  |- context[getL(getU _)] ] => rewrite getLgetU
 | [ H: context[getU(_++_)] |- _ ] => setoid_rewrite getUApp in H
 | [ H: context[getL(_++_)] |- _ ] => setoid_rewrite getLApp in H
 | [ H: context[getU(getU _)] |- _ ] => rewrite getU_fixpoint in H
 | [ H: context[getL(getL _)] |- _ ] => rewrite getL_fixpoint in H
 | [ H: context[getU(getL _)] |- _ ] => rewrite getUgetL in H
 | [ H: context[getL(getU _)] |- _ ] => rewrite getLgetU in H
 
(*  | [ H: SetU ?K  |- context[getU ?K] ] => rewrite setUtoGetU;auto
 | [ H1: SetU ?K, H2:context[getU ?K]  |- _ ] => rewrite setUtoGetU in H2;auto  *)

 (* About getU, getL and PlusT *)
 | [  |- context[getU (PlusT (getL _))] ] => rewrite getUgetLPlusT
 | [  |- context[getL (PlusT (getU _))] ] => rewrite getLgetUPlusT
 | [  |- context[getU (PlusT (getU _))] ] => rewrite getUPlusTgetU'
 | [  |- context[getL (PlusT (getL _))] ] => rewrite getUPlusTgetL'
 | [ H: context[getU (PlusT (getL _))]  |- _ ] => rewrite getUgetLPlusT in H
 | [ H: context[getL (PlusT (getU _))]  |- _ ] => rewrite getLgetUPlusT in H  
 | [ H: context[getU (PlusT (getU _))]  |- _ ] => rewrite getUPlusTgetU' in H  
 | [ H: context[getL (PlusT (getL _))]  |- _ ] => rewrite getUPlusTgetL' in H 
  
 | [ H: SetU ?K |- context[getL (PlusT ?K)] ] => rewrite (getLgetUPlusT' H);auto  
 | [ H: SetT ?K |- context[getU (PlusT ?K)] ] => rewrite <- (getUPlusT H);auto  
 | [ H: SetT ?K |- context[getL (PlusT ?K)] ] => rewrite <- (getLPlusT H);auto
 | [ H1: SetU ?K, H2: context[PlusT (getU ?K)] |- _ ] => rewrite (setUPlusTgetU H1) in H2;auto 
 | [ H1: SetU ?K, H2: context[getL (PlusT ?K)] |- _ ] => rewrite (getLgetUPlusT' H1) in H2;auto  
 | [ H1: SetT ?K, H2: context[getU (PlusT ?K)] |- _ ] => rewrite <- (getUPlusT H1) in H2;auto  
 | [ H1: SetT ?K, H2:context[getL (PlusT ?K)]  |- _] => rewrite <- (getLPlusT H1) in H2;auto
  | [  |- context[(second (getU ?K++getL ?K))] ] => rewrite <- cxtDestructSecond
 | [ H:context[(second (getU ?K++getL ?K))] |- _ ] => rewrite <- cxtDestructSecond in H

 
end. 

Ltac solveSignature2 :=
 match goal with
  | [ |- SetU (getU _) ] => apply getUtoSetU
  | [ |- SetU (Loc _) ] => apply SetULoc  
  | [ |- SetT (Loc _) ] => apply SetTLoc    
  | [ |- SetL (getL _) ] => apply getLtoSetL
  | [ H: SetK4 ?i ?K |- SetK4 ?i (getU ?K)] => apply SetK4Destruct in H;sauto
  | [ H: SetK4 ?i ?K |- SetK4 ?i (getL ?K)] => apply SetK4Destruct in H;sauto
  | [ H: SetK ?i ?K |- SetK ?i (getU ?K)] => apply SetKDestruct in H;sauto
  | [ H: SetK ?i ?K |- SetK ?i (getL ?K)] => apply SetKDestruct in H;sauto

| [ H: SetK4 ?i ?K, H2: Permutation (getU ?K) (?K2 ++ _) |- SetK4 ?i ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 | [ H: SetK4 ?i ?K, H2: Permutation (getU ?K) (_ ++ ?K2) |- SetK4 ?i ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2

 | [ H: SetK ?i ?K, H2: Permutation (getU ?K) (?K2 ++ _) |- SetK ?i ?K2] => 
   let H' := fresh "H" in
          apply SetKDestruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 | [ H: SetK ?i ?K, H2: Permutation (getU ?K) (_ ++ ?K2) |- SetK ?i ?K2] => 
   let H' := fresh "H" in
          apply SetKDestruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 
 | [ H: SetU (PlusT ?K) |- SetU ?K ] => apply PlusTSetU;auto 
 | [  |- SetU (PlusT _ )] => apply SetUPlusT;solveSignature2

  | [H: Permutation (getU ?CN) (_ ++ ?M) |- SetU ?N] =>  apply getUPerm_SetU in H;solveSignature2
  | [H: Permutation (getU ?CN) (?M ++ _) |- SetU ?M] =>  apply getUPerm_SetU in H;solveSignature2

 | [ H: SetT ?K |- SetT (getU ?K)] => rewrite cxtDestruct in H;solveSignature2
 | [ H: SetT ?K |- SetT (getL ?K)] => rewrite cxtDestruct in H;solveSignature2
 

  | [ |- SetU (PlusT _) ] => apply SetUPlusT
  | [ |- SetK4 (plust _) (PlusT _) ] => apply SetK4PlusT
  | [ |- SetK (plust _) (PlusT _) ] => apply SetKPlusT 
  
 | [ H1: u ?i = false, H2: In (?i, ?F) ?B  |- In (?i, ?F) (getL ?B) ] => apply lIngetL;auto

 | [ H1: u ?i = true, H2: SetK ?i ?K  |- SetU ?K  ] => eapply (SetUKClosure H1);auto
 | [ H1: mt ?i = true, H2: SetK ?i ?K  |- SetT ?K  ] => eapply (SetTKClosure H1);auto 
 | [ H1: u ?i = true, H2: SetK4 ?i ?K  |- SetU ?K  ] => eapply (SetUK4Closure H1);auto
 | [ H1: mt ?i = true, H2: SetK4 ?i ?K  |- SetT ?K  ] => eapply (SetTK4Closure H1);auto 

 | [ H1: u ?i = true, H2: SetK ?i ?K  |- SetU (_ ?K)  ] => eapply (SetUKClosure H1);simplSignature
 | [ H1: mt ?i = true, H2: SetK ?i ?K  |- SetT (_ ?K)  ] => eapply (SetTKClosure H1);simplSignature 
 | [ H1: u ?i = true, H2: SetK4 ?i ?K  |- SetU (_ ?K)  ] => eapply (SetUK4Closure H1);simplSignature
 | [ H1: mt ?i = true, H2: SetK4 ?i ?K  |- SetT (_ ?K)  ] => eapply (SetTK4Closure H1);simplSignature 
 | [ H: SetU ?K |- context[PlusT (getU ?K)] ] => try solve [rewrite setUPlusTgetU;auto]

end.

Ltac solveSignature :=
simplSignature;
try solve [solveSignature1];
try solve [solveSignature2];
try
match goal with
 | [ |- SetK ?i ?K] => solveFoldFALL2 (fun k :subexp*oo => m4 (fst k) = false /\ lt i (fst k) )
 | [ |- SetK4 ?i ?K] => solveFoldFALL2  (fun k :subexp*oo => m4 (fst k) = true /\ lt i (fst k) )
 | [ |- SetT ?K] => solveFoldFALL1 (fun k :subexp*oo => mt (fst k) = true)
 | [ |- SetU ?K] => solveFoldFALL1 (fun k :subexp*oo => u (fst k) = true)
 | [ |- SetL ?K] => solveFoldFALL1 (fun k :subexp*oo => u (fst k) = false)
 end;try sfold.  

Ltac solveIsFormula1 := auto;try
  match goal with
  | [ H1: isFormulaL (second ?L), H2: In (_,?P) ?L  |- isFormula ?P ] => apply isFormulaInS1 in H2;auto
  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A _) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ _ ?A) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A) ?L  |- isFormula (?A _) ] => apply isFormulaInS1 in H2;solveIsFormula1
 
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,?P)::_)  |- isFormula ?P ] => apply isFormulaInS2 in H2;auto
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A _)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ _ ?A)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A)::_)  |- isFormula (?A _) ] => apply isFormulaInS2 in H2;solveIsFormula1

  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th ?P  |- isFormula ?P ] => apply H1 in H2;auto
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A _)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ _ ?A)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A)  |- isFormula (?A _) ] => apply H1 in H2;solveIsFormula1
 
  | [ H: isFormula (_ ?A _) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ _ ?A) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ ?A) |- isFormula (?A _) ] => inversion H;subst;eauto
  
  | [ H: isFormulaL ((_ ?A _)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ _ ?A)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ ?A)::_) |- isFormula (?A _) ] => inversion H;subst;eauto
end.

Ltac solveIsFormula2 := auto;try
  match goal with

  | [  |- isFormulaL (second (PlusT (getU _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (PlusT (getL _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (Loc (getU _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (Loc (getL _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (PlusT _)) ] => try solve [apply isFormulaL_PlusT;auto]
  | [  |- isFormulaL (second (Loc _)) ] => try solve [apply isFormulaL_Loc;auto]
  | [  |- isFormulaL (second (getU _)) ] => try solve [apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (getL _)) ] => try solve [apply isFormulaL_getL;auto]
  
  | [ H1: Permutation (getL ?mBD) (getL ?mB ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mD),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mD)] => eapply @isFormulaSecondSplit2 with (X:=nil) (Y:=nil) (BD:=mBD) (B:=mB);sauto
  | [ H1: Permutation (getL ?mBD) (getL ?Bm ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mB),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mB)] => eapply @isFormulaSecondSplit1 with (X:=nil) (Y:=nil) (BD:=mBD) (D:=mD);sauto
end.


Ltac SLFormulaSolve := auto; try solve[solveIsFormula1];
match goal with
 | [ |- isFormulaL ?K] => simpl;solveFoldFALL1 isFormula;solveIsFormula1
end.

Ltac SLSolve := do 2 
 solveSignature; try
 match goal with
 | |- isFormulaL (second ?K) => simplSignature;solveIsFormula2;SLFormulaSolve
 | |- isFormulaL ?K => simplSignature;SLFormulaSolve
    end;sfold.
 
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


(* Ltac simplF := 
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
 
 | [  |- context[PlusT(_++_)] ] => setoid_rewrite PlusTApp
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

 
 | [ H: context[PlusT(_++_)] |- _ ] => setoid_rewrite PlusTApp in H 
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
 *)
   
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
    | [ |- uniform _ ] => solve [solveUniform]
    | [ |- _ <= _ ] => lia
    | [ |- _ >= _ ] => lia
    | [ |- _ < _ ] => lia
    | [ |- _ > _ ] => lia                       
    | [|- ~ asynchronous _] => first [solve [intro H; inversion H;auto] | auto] 
    | [|- ~ IsPositiveAtom _ ] => first [solve [intro H; inversion H;auto] | auto] 
    | [|- IsPositiveAtom _ ] => repeat constructor
    | [|- release _] => first [solve [constructor] | auto]  
    | [|- asynchronous _] => first [solve [constructor] | auto]

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
    | [H: seqN _ _ _ _  (>> zero) |- _ ] => inversion H
    | [H: seq  _ _ _  (>> zero) |- _ ] => inversion H
    | [ |- _ >= _] => subst; lia
    | [ |- _ <= _] => subst; lia
    end;auto;
  try(match goal with
      | [ |- Permutation _ _] => simplSignature; perm
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
                         | [ |- seq _ _ _ _ ] =>  apply tri_par'
                         | [|- seqN _ _ _ _ _] => apply tri_par
                         end.

Tactic Notation "release" := match goal with
                         | [ |- seq _ _ _ _ ] =>  apply tri_rel' ;solveF
                         | [|- seqN _ _ _ _ _] => apply tri_rel ;solveF
                         end.

  
Tactic Notation "init1"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_init1';try SLSolve;auto
                          | [|- seqN _ _ _ _ _] => apply tri_init1;try SLSolve;auto
                          end.


Tactic Notation "init2" constr(a) constr(b) := match goal with
                          | [ |- seq _ _ _ _ ] =>  eapply @tri_init2' with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
                          | [|- seqN _ _ _ _ _] => eapply @tri_init2 with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
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
          
    | [|- seqN _ _ _ [] (>>  One)] => apply tri_one;try SLSolve;auto
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
      | Bang loc _ => apply tri_bangL;try SLSolve;solvell
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
    
    | [|- seq _ _ [] (>>  One)] => apply tri_one';try SLSolve;auto
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
      | Bang loc _ => apply tri_bangL';try SLSolve;solvell'
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
Tactic Notation "decide1" := match goal with
                                        | [ |- seq _ _ (?P::_) _ ] =>  eapply @tri_dec1' with (F:= P);solveF;solveLL
                                        | [|- seqN _ _ _ (?P::_) _] => eapply @tri_dec1 with (F:= P);solveF;solveLL 
                                        end;solveF.
                      
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

  Lemma allSeTU (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) B : SetU B.
Proof with auto.
 induction B...
 apply Forall_cons... 
 apply allU.
Qed.

Lemma allSeTLEmpty (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) (B : list TypedFormula) : getL B = (@nil TypedFormula).
Proof with auto.
 rewrite (SetU_then_empty (allSeTU SIU B));auto.
Qed.

Lemma permSeTL (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) (B : list TypedFormula) : Permutation (getL B) (getL B ++ getL B).
Proof with auto.
 rewrite allSeTLEmpty...
Qed.

Global Hint Resolve allSeTU permSeTL : core. 

 Lemma tensorU (OLS: OLSig) (SI : Signature) (USI : UnbSignature) n th B MN M N F G:          
  Permutation MN (M ++ N) ->
  seqN th n B M (>> F) ->
  seqN th n B N (>> G) -> seqN th (S n) B MN (>> F ** G).
  Proof.   
  intros.
  tensor M N.
  Qed.

 Lemma tensorU' (OLS: OLSig) (SI : Signature) (USI : UnbSignature) th B MN M N F G:          
  Permutation MN (M ++ N) ->
  seq th B M (>> F) ->
  seq th B N (>> G) -> seq th B MN (>> F ** G).
  Proof.   
  intros.
  tensor M N.
  Qed.

Tactic Notation "tensorUnb"  constr(Ctx1) constr(Ctx2) := match goal with
               | [ |- seq _ _ _ _ ] =>  eapply @tensorU' with (M:=Ctx1) (N:=Ctx2);solveF;solveLL
               | [|- seqN _ _ _ _ _] => eapply @tensorU with (M:=Ctx1) (N:=Ctx2);solveF;solveLL
                 end.


Tactic Notation "copyK4"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _ ] => eapply @tri_copyK4' with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyK4 with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
                                                       end.
                                                      
Tactic Notation "copyUK"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyUK' with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyUK with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
                                                       end. 
                                                       
Tactic Notation "copyLK"  constr(i) constr(P) constr(B) := match goal with
                                                       | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyLK' with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
                                                       | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyLK with (b:=i) (F:=P) (B':=B);try SLSolve;solveF;solveLL
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
  sauto;do 2 simplSignature;cleanF;solveF;sauto.

