Require Export MMLL.Misc.Hybrid.
Require Export MMLL.SL.FLLTactics.
Require Export MMLL.OL.CutCoherence.OLSyntax.
Require Export MMLL.OL.CutCoherence.OLDefinitions.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

 
Ltac OLfold := 
repeat
match goal with
 | [  |- context[Forall IsPositiveAtomFormula ?L] ] => change (Forall IsPositiveAtomFormula L) with (IsPositiveAtomFormulaL L)
 | [ H : context[Forall IsPositiveAtomFormula ?L] |- _ ] => fold (IsPositiveAtomFormulaL L) in H 
 | [  |- context[Forall isOLFormula ?L] ] => change (Forall isOLFormula L) with (isOLFormulaL L)
 | [ H : context[Forall isOLFormula ?L] |- _ ] => fold (isOLFormulaL L) in H                 

 | [  |- context[map (fun x => d| x|) ?L] ] => change (map (fun x => d| x|) L) with (LEncode L)
 | [ H : context[map (fun x => d| x|) ?L] |- _ ] => fold (LEncode L) in H                 
 | [  |- context[map (fun x => u| x|) ?L] ] => change (map (fun x => u| x|) L) with (REncode L)
 | [ H : context[map (fun x => u| x|) ?L] |- _ ] => fold (REncode L) in H                 
 | [  |- context[map (fun x => (?i,x)) ?L] ] => change (map (fun x => (?i,x)) L) with (CEncode i L)
 | [ H : context[map (fun x => (?i,x)) ?L] |- _ ] => fold (CEncode i L) in H                 
end.


Ltac solveCEncode :=
  match goal with
  | [H1: u ?i = true |- SetU (CEncode ?i ?L) ] => apply setUCEncode;auto
  | [ |- SetU (CEncode loc ?L) ] => apply setUCEncode;apply locu
  | [H1: u ?i = true |- Forall (fun k : subexp * oo => u (fst k) = true) (CEncode ?i ?L) ] => apply setUCEncode;auto
  | [ |- Forall (fun k : subexp * oo => u (fst k) = true) (CEncode loc ?L) ] => apply setUCEncode;apply locu
 
  
  | [H1: mt ?i = true |- SetT (CEncode ?i ?L) ] => apply setTCEncode;auto
  | [  |- SetT (CEncode loc ?L) ] => apply setTCEncode;apply locT
 
  | [H: context[second (CEncode ?i ?L)] |- _ ] => rewrite !secCEncode in H
  | [ |- context[second (CEncode ?i ?L)] ] => rewrite !secCEncode
  | [ |- context[getU (CEncode ?i ?L)] ] => rewrite !setUtoGetU 
  | [H: context[getU (CEncode ?i ?L)] |- _ ] => rewrite !setUtoGetU in H 
  | [ |- context[getL (CEncode ?i ?L)] ] => rewrite !SetU_then_empty;auto;solveCEncode
  | [H: context[getL (CEncode ?i ?L)] |- _ ] => rewrite !SetU_then_empty in H;auto;try solveCEncode 
 | [H1: Permutation (?F::?D') ?D |- Permutation ((d| ?F |)::(LEncode ?D')) (LEncode ?D) ] => apply Remove_LEncode;auto
 | [H1: Permutation (?F::?D') ?D |- Permutation ((u| ?F |)::(REncode ?D')) (REncode ?D) ] => apply Remove_REncode;auto
 
  end.
 

Ltac solveOLFormulas := auto;try
  match goal with
  | [  |- IsPositiveAtomFormula (atom _)] => constructor;solveOLFormulas 
  | [ H:  IsPositiveAtomFormula (atom (_ (?A))) |- isOLFormula ?A] => inversion H;subst;auto
  | [ H:  isOLFormulaL (?A::_) |- isOLFormula ?A] => inversion H;subst;auto
  | [H : isOLAtom ?A |-  isOLFormula ?A] => inversion H;subst;auto
  | [ H:  isOLFormula (t_bin _ _ ?A) |- isOLFormula ?A] => inversion H;subst;auto;clear H;solveOLFormulas
  | [ H:  isOLFormula (t_bin _ ?A _) |- isOLFormula ?A] => inversion H;subst;auto;clear H;solveOLFormulas
  | [ H:  isOLFormula (t_ucon _ ?A) |- isOLFormula ?A] => inversion H;subst;auto;clear H;solveOLFormulas
  | [ H : isOLFormula (t_quant _ ?FX) |- isOLFormula (?FX _) ] => inversion H;subst;clear H;[solveOLFormulas|];
   match goal with
                [ H': lbind 0 _ = lbind 0 _ |- _] =>
                apply lbindEq in H';auto;rewrite <- H';auto
              end 
  | [ H:  isOLAtom (t_atom _ ?t) |- isOLTerm ?t] => inversion H;subst;auto
  | [ H:  isOLConstant _ |- _] => try solve [inversion H]
  | [ H:  isOLTerm _ |- _] => try solve [inversion H]

  | [ H:  isOLFormulaL ((t_bin _ _ ?A)::_) |- isOLFormula ?A] => inversion H;subst;auto;clear H;solveOLFormulas
  | [ H:  isOLFormulaL ((t_bin _ ?A _)::_) |- isOLFormula ?A] => inversion H;subst;auto;clear H;solveOLFormulas
  | [ H:  isOLFormulaL ((t_ucon _ ?A)::_) |- isOLFormula ?A] => inversion H;subst;clear H;solveOLFormulas
  | [ H : isOLFormulaL ((t_quant _ ?FX)::_) |- isOLFormula (?FX _) ] => inversion H;subst;clear H;solveOLFormulas  

  | [ H:  IsPositiveAtomFormula (atom (_ (?A))) |- isOLFormula ?A] => inversion H;subst;auto
  | [H : isOLFormulaL ?L |-  IsPositiveAtomFormulaL (LEncode ?L)] => solve [apply (isOLLEncode H);auto]
  | [H : isOLFormulaL ?L |-  IsPositiveAtomFormulaL (REncode ?L)] => solve [apply (isOLREncode H);auto]
   
 end.


Ltac OLSolve := try solve[solveOLFormulas];
try
match goal with
 | [ |- IsPositiveAtomFormulaL (_::?K)] => simpl;solveFoldFALL1 IsPositiveAtomFormula;[solveOLFormulas | OLfold;OLSolve]
 | [ |- IsPositiveAtomFormulaL ?K] => simpl;solveFoldFALL1 IsPositiveAtomFormula;solveOLFormulas
 | [ |- isOLFormulaL (_::?K)] => simpl;solveFoldFALL1 isOLFormula;[solveOLFormulas | OLfold;OLSolve]
 | [ |- isOLFormulaL ?K] => simpl;solveFoldFALL1 isOLFormula;solveOLFormulas
 | [ H: isOLFormulaL (?A::_) |- IsPositiveAtomFormula (atom (_ _))] => 
         inversion H;subst;OLSolve 

 end;OLfold.


Ltac solveQF :=
  match goal with
   [ H1 : isOLFormula (t_quant ?qt ?FX), 
     H2 : proper ?x |- isOLFormula (?FX ?x)] =>
                inversion H1;subst;OLSolve;
                match goal with
       [ H : lbind 0%nat _ = lbind 0%nat ?FX |-
          isOLFormula (?FX ?x)] =>
                apply lbindEq in H;sauto;
               try rewrite <- H;sauto
              end  
                
   end.  
 
 (** During the proof of cut-elimination, there are many
          subgoals related to [IsPositiveAtomFormulaL] predicates and
          testing whether a rule belongs to the theory. This procedure
          resolves most of these cases. Moreover, since the classical
          and linear context only contain positive atoms, none of the
          proofs (by inversion) may use [tri_dec1] nor [tri_dec2]. *)
(*   Ltac CutTac :=
    solveLL; 
    repeat 
      match goal with
      | [H : seqN _ _ _ (?L ++ [atom ?F ]) (> []) |- _] => rewrite (Permutation_app_comm L [atom F ]) in H
      | [ H :  Permutation (?F :: ?N) (?G :: ?F :: ?M) |- _ ] => apply Perm_swap_inv in H
      (* Positive Atom cases *)
      | [ |-  IsPositiveAtomFormulaL _ ] => solve  IsPositiveLSolve 
      | [ H : isOLAtom ?A |- Forall IsPositiveAtomFormula [atom (up ?A) ] ]=>
        repeat constructor;inversion H3;auto
      (* the following 3 cases solve the goal when the case of Dec1 appears *)
      | [  H1 : IsPositiveAtomFormulaL ?L , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F ((_ ++ ?N)) _ |- _ ] =>
        apply Remove_In in H3; destruct H3;solveF;
        apply  Forall_forall  with (x:= F) in H1;auto;destruct H1;solveF
      | [  H1 : IsPositiveAtomFormulaL ?N , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F ?N _ |- _ ] =>
        apply Remove_In in H3;apply  Forall_forall  with (x:= F) in H1;auto;destruct H1;solveF
      | [  H1 : IsPositiveAtomFormulaL ?N , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F (_ :: ?N) _ |- _ ] =>
        apply Remove_In in H3;destruct H3;subst;solveF
      | [ HIn :  In ?F ?B , HB : IsPositiveAtomFormulaL ?B , Hneg : ~ IsPositiveAtom ?F |- _]
        => let HB' := fresh in
           apply Forall_forall with (x:= F) in HB as HB';auto;subst;inversion HB';solveF
      | [ HPos : IsPositiveAtomFormulaL ?N, HRem : Remove ?F ([ atom (up ?A)  ] ++ ?N) _, HNeg : ~ IsPositiveAtom ?F |- _] => let H' := fresh "H" in generalize (Remove_In HRem);intro H';inversion H2;subst;solveF;IsPositiveLSolve
      | [ H : Permutation  (?F :: ?N) ( (?F :: ?M1) ++ ?M2) |- _ ] =>
        simpl in H; apply Permutation_cons_inv in H
      | [ H :  Permutation (?F :: ?N) (?X ++ ?F :: ?M) |- _ ] =>
        apply Perm_swap_inv_app in H
      end.
 *)