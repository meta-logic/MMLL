Require Export MMLL.Misc.UtilsTactics.
Require Export MMLL.OL.CutCoherence.LNSi.LJBipoles.
Require Export MMLL.SL.FLLReasoning.
Require Export MMLL.SL.InvPositivePhase.
         
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section LJInv.

Context {SI: Signature}.
Context {Unb: UnbSignature}.
Context {UnbD: UnbNoDSignature}.

  Theorem InvTT:  forall n a B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
    seqN (LJ a) n ((a,d| t_cons TT|)::B) M (UP []) -> seq (LJ a) B M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros.
      inversion H1...
      inversion H2...
       apply RemoveNotPos1 in H5...
       intro Hc. inversion Hc;inversion H4...
       inversion H7...
       contradict H6.
       constructor.
       apply InUNotPos in H3...
       rewrite allU in H4...
       2:{ solveSignature1. }
       inversion H4...
       + inversion H3...
           - apply BipoleReasoning in H6...
             simpl in H11.
             inversion H10...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H12.
             checkPermutationCases H12.
             inversion H10...
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             inversion H10...
             solveF.
             inversion H10...
             solveF.
           - apply BipoleReasoning in H6...
             inversion H10...
             solveF.
             inversion H10...
             solveF.
           - apply BipoleReasoning in H6...
             simpl in H11.
             inversion H10...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF| ] x0.
             simpl... 
             simpl in H12.
             checkPermutationCases H12.
             inversion H10...
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
       + inversion H3...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingWith in H10...
             apply H in H10, H12...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor [u| t_bin AND F0 G| ] x0.
             simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingWith in H10...
             apply H in H13, H14...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingPlus in H10...
             1-2: apply H in H9...
             1-2:TFocus (BinBipole AND_BODY Left F0 G).
             1-2:LLTensor [d| t_bin AND F0 G| ] x0.
             1-2:simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingPlus in H10...
             1-2: apply H in H12...
             1-2:TFocus (BinBipole AND_BODY Left F0 G).
             1-2:LLTensor (@nil oo) M.
             1,3: LLrew2 H8.
             1,2: init2 x0 x2.
             1,2: simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingPlus in H10...
             1-2: apply H in H9...
             1-2:TFocus (BinBipole OR_BODY Right F0 G).
             1-2:LLTensor [u| t_bin OR F0 G| ] x0.
             1-2:simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingPlus in H10...
             1-2: apply H in H12...
             1-2:TFocus (BinBipole OR_BODY Right F0 G).
             1-2:LLTensor (@nil oo) M.
             1,3: LLrew2 H8.
             1,2: init2 x0 x2.
             1,2: simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingWith in H10...
             apply H in H10, H12...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor [d| t_bin OR F0 G| ] x0.
             simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingWith in H10...
             apply H in H13, H14...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             simpl in H13.
             apply FocusingBangPar in H12...
             checkPermutationCases H11.
             LLrew1 H10 H18.
             apply H in H18...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld. solveSignature1.
             apply GenK4RelUT' with (C4:= x) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
             rewrite H10 in H14. solveSE.
             rewrite H10 in H15. solveSE.
             rewrite H10 in H16. solveLT.
             simpl...
             symmetry in H11.
             srewrite H11 in H1.
             rewrite map_app in H1. OLSolve.
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld. solveSignature1.
             apply GenK4RelUT' with (C4:= x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             simpl...
             LLPar. do 2 LLStore.
             HProof.
             
             simpl in H14.
             checkPermutationCases H14.
             apply FocusingBangPar in H12...
             checkPermutationCases H14.
             LLrew1 H12 H20.
             apply H in H20...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor.
             LLrew2 H10. 
             init2 x0 x2.
             simpl... createWorld. solveSignature1.
             apply GenK4RelUT' with (C4:= x) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
             rewrite H12 in H16. solveSE.
             rewrite H12 in H17. solveSE.
             rewrite H12 in H18. solveLT.
             simpl...
             symmetry in H14.
             srewrite H14 in H1.
             rewrite map_app in H1. OLSolve.
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor.
             LLrew2 H10. 
             init2 x0 x2.
             simpl... createWorld. solveSignature1.
             apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             simpl...
             LLPar. do 2 LLStore.
             HProof.
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingTensor in H10...
             apply H in H9, H13...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H10 in H11.
             1-2: rewrite H11 in H0.
             1-2: inversion H0...
             
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingTensor in H10...
             apply H in H12, H15...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H6...
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H9. 
             TFocus (CteBipole TT_BODY Right).
             apply ooth_consC.
             constructor...
             inversion H6.
             LLTensor [u| t_cons TT |] (@nil oo).
             simpl...
             TFocus (RINIT OO).
             LLTensor [u| OO |] (@nil oo).
             LLrew2 H7. 
             init2 x x1.
           - checkPermutationCases H9. 
             TFocus (RINIT OO).
             LLTensor  (@nil oo) [d| OO |].
             LLrew2 H7. 
             init2 x x1.
           - checkPermutationCases H9. 
             checkPermutationCases H7.
             TFocus (CteBipole TT_BODY Right).
             apply ooth_consC.
             constructor...
             inversion H6.
             LLTensor.
             LLrew2 H9. 
             init2 x0 x3.
             simpl...
             TFocus (RINIT OO).
             LLTensor. 
             init2 x0 x3.
             init2 x x4.
       +   apply BipoleReasoning in H6...
             apply FocusingQuest in H9...
             LLSwapC H8. 
             apply H in H8...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             simpl in H11.
             checkPermutationCases H11.
             apply FocusingQuest in H9...
             
             apply contractionN with (F:=(a, d| t_cons TT_BODY.(cte) |)) in H9...
             apply H in H9...
             solveSignature1.
             simpl...
             apply FocusingQuest in H9...
             LLSwapC H11.
             apply H in H11...
             TFocus (POS OO a).
             LLTensor (@nil oo) M.
             LLrew2 H7. 
             init2 x0 x2.
       +   apply BipoleReasoning in H6...
             apply FocusingQuest in H9...
             LLSwapC H8. 
             apply H in H8...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             simpl in H11.
             checkPermutationCases H11.
             apply FocusingQuest in H9...
             LLSwapC H11.
             apply H in H11...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M.
             LLrew2 H7. 
             init2 x0 x2.
 Qed.            
 
  Theorem InvFF:  forall n a B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
    seqN (LJ a) n ((loc,u| t_cons FF|)::B) M (UP []) -> seq (LJ a) B M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros.
      inversion H1...
      inversion H2...
       apply RemoveNotPos1 in H5...
       intro Hc. inversion Hc;inversion H4...
       inversion H7...
       contradict H6.
       constructor.
       apply InUNotPos in H3...
       rewrite allU in H4...
       2:{ solveSignature1. }
       inversion H4...
       + inversion H3...
           - apply BipoleReasoning in H6...
             simpl in H11.
             inversion H10...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H12.
             checkPermutationCases H12.
             inversion H10...
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             inversion H10...
             solveF.
             inversion H10...
             solveF.
           - apply BipoleReasoning in H6...
             inversion H10...
             solveF.
             inversion H10...
             solveF.
           - apply BipoleReasoning in H6...
             simpl in H11.
             inversion H10...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF| ] x0.
             simpl... 
             simpl in H12.
             checkPermutationCases H12.
             inversion H10...
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
       + inversion H3...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingWith in H10...
             apply H in H10, H12...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor [u| t_bin AND F0 G| ] x0.
             simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingWith in H10...
             apply H in H13, H14...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingPlus in H10...
             1-2: apply H in H9...
             1-2:TFocus (BinBipole AND_BODY Left F0 G).
             1-2:LLTensor [d| t_bin AND F0 G| ] x0.
             1-2:simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingPlus in H10...
             1-2: apply H in H12...
             1-2:TFocus (BinBipole AND_BODY Left F0 G).
             1-2:LLTensor (@nil oo) M.
             1,3: LLrew2 H8.
             1,2: init2 x0 x2.
             1,2: simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingPlus in H10...
             1-2: apply H in H9...
             1-2:TFocus (BinBipole OR_BODY Right F0 G).
             1-2:LLTensor [u| t_bin OR F0 G| ] x0.
             1-2:simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingPlus in H10...
             1-2: apply H in H12...
             1-2:TFocus (BinBipole OR_BODY Right F0 G).
             1-2:LLTensor (@nil oo) M.
             1,3: LLrew2 H8.
             1,2: init2 x0 x2.
             1,2: simpl...
           - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingWith in H10...
             apply H in H10, H12...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor [d| t_bin OR F0 G| ] x0.
             simpl...
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingWith in H10...
             apply H in H13, H14...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H6...
             simpl in H13.
             apply FocusingBangPar in H12...
             checkPermutationCases H11.
             rewrite H10 in H14.
             inversion H14... solveSignature1.
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             apply seqNtoSeq in H18.
             simpl...
             
             checkPermutationCases H14.
             apply FocusingBangPar in H12...
             checkPermutationCases H14.
             rewrite H12 in H16.
             inversion H16... solveSignature1.
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor.
             LLrew2 H10. 
             init2 x0 x2.
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             apply seqNtoSeq in H20.
             simpl...
            - apply BipoleReasoning in H6...
             simpl in H11.
             apply FocusingTensor in H10...
             apply H in H9, H13...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H10 in H11.
             1-2: rewrite H11 in H0.
             1-2: inversion H0...
             
             simpl in H12.
             checkPermutationCases H12.
             apply FocusingTensor in H10...
             apply H in H12, H15...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H8. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H6...
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H9. 
             TFocus (RINIT OO).
             LLTensor  [u| OO |]  (@nil oo).
             LLrew2 H7. 
             init2 x x1.
           - checkPermutationCases H9. 
             TFocus (CteBipole FF_BODY Left).
             apply ooth_consC.
             constructor...
             inversion H6.
             LLTensor [d| t_cons FF |] (@nil oo) .
             simpl...
             TFocus (RINIT OO).
             LLTensor (@nil oo)  [d| OO |] .
             LLrew2 H7. 
             init2 x x1.
           - checkPermutationCases H9. 
             checkPermutationCases H7.
             TFocus (CteBipole FF_BODY Left).
             apply ooth_consC.
             constructor...
             inversion H6.
             LLTensor.
             LLrew2 H7. 
             init2 x x0.
             simpl...
             checkPermutationCases H7.
             TFocus (RINIT OO).
             LLTensor. 
             init2 x0 x3.
             init2 x x4.
       +   apply BipoleReasoning in H6...
             apply FocusingQuest in H9...
             LLSwapC H8. 
             apply H in H8...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             simpl in H11.
             checkPermutationCases H11.
             apply FocusingQuest in H9...
             
             LLSwapC H11.
             apply H in H11...
             TFocus (POS OO a).
             LLTensor (@nil oo) M.
             LLrew2 H7. 
             init2 x0 x2.
       +   apply BipoleReasoning in H6...
             apply FocusingQuest in H9...
             LLSwapC H8. 
             apply H in H8...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             simpl in H11.
             checkPermutationCases H11.
             apply FocusingQuest in H9...
              apply contractionN in H9...
             apply H in H9...
             solveSignature1.
            
             apply FocusingQuest in H9...
             LLSwapC H11.
             apply H in H11...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M.
             LLrew2 H7. 
             init2 x0 x2.
 Qed.            
 
 
  Theorem InvIMPR:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
   mt a = true ->
   m4 a = true ->
    seqN (LJ a) n ((loc,u| t_bin IMP P Q|) :: (a,d| P| )::  (loc,u| Q| )::B) M (UP []) -> seq (LJ a) ((a,d| P| ):: (loc,u| Q| ):: B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB Hta H4a HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       inversion H6...
       contradict H3.
       constructor.
       
       apply InUNotPos in H7...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            simpl in H9.
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H7...
               checkPermutationCases H5.
               rewrite H4 in H9.
               inversion H9...
               solveSignature1. 
               checkPermutationCases H5.
               checkPermutationCases H7.
               rewrite H7 in H5.
               rewrite H5 in H9.
               inversion H9...
               inversion H15...
               solveSignature1. 
               LLSwap.
               apply weakening;solveSignature1...
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
                        rewrite <- H8...
                        rewrite H5...
              apply seqNtoSeq in H13.           
              simpl... 
              checkPermutationCases H7.
               rewrite H7 in H9.
               inversion H9...
               solveSignature1. 
               LLSwap.
               apply weakening;solveSignature1...
               apply weakening;solveSignature1...
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
              apply seqNtoSeq in H13.           
              simpl... }
             { 
               checkPermutationCases H9.
               +
               clear H8.
                apply FocusingBangPar in H7...
               checkPermutationCases H7.
               rewrite H4 in H9.
               inversion H9...
               solveSignature1. 
               checkPermutationCases H7.
               checkPermutationCases H8.
               rewrite H8 in H7.
               rewrite H7 in H9.
               inversion H9...
               inversion H16...
               solveSignature1. 
               apply AbsorptionC';solveSignature1...
               LLSwap.
               apply AbsorptionL';solveSignature1...
               rewrite <- H12.
               LLPerm  (x4++(a, d| P |) :: x1).
               apply weakeningGen...
               rewrite <- H7.
               HProof.
               checkPermutationCases H8.
               rewrite H8 in H9.
               inversion H9...
               solveSignature1. 
               apply AbsorptionL';solveSignature1...
               apply AbsorptionL';solveSignature1...
               rewrite <- H12.
               LLPerm  (x4++x2).
               apply weakeningGen...
               HProof.
               + 
               clear H8.
                apply FocusingBangPar in H7...
               checkPermutationCases H8.
               rewrite H7 in H10.
               inversion H10...
               solveSignature1. 
               checkPermutationCases H8.
               checkPermutationCases H9.
               rewrite H9 in H8.
               rewrite H8 in H10.
               inversion H10...
               inversion H17...
               solveSignature1.
              TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               simpl...  init2 x0 x2.
                LLSwap.
               apply weakening;solveSignature1...
              
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x4) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
                rewrite <- H13...
                rewrite H8...        
              apply seqNtoSeq in H14.           
              simpl... 
              
               checkPermutationCases H9.
               rewrite H9 in H10.
               inversion H10...
               solveSignature1.
              TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               simpl...  init2 x0 x2.
               apply weakening;solveSignature1...
              apply weakening;solveSignature1...
              
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x4) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
              apply seqNtoSeq in H14.           
              simpl... 
              
              }
             - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5. 
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H6.
              TFocus (RINIT OO).
              LLTensor [u| OO |] (@nil oo).
              init2 x x1.
           - checkPermutationCases H6.
             TFocus (BinBipole (IMP_BODY a) Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [d| t_bin IMP P Q |] (@nil oo)  .
             simpl...
              LLTensor; LLRelease;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| P |] (@nil oo).
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| Q |] .
             apply weakening;solveSignature1.
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor (@nil oo)  [ d| OO |].
             apply weakening;solveSignature1.
             solveLL.
            - checkPermutationCases H6.
             checkPermutationCases H4.
             TFocus (BinBipole (IMP_BODY a) Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             init2 x x0.
             rewrite H4...
              LLTensor; LLRelease;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| P |] (@nil oo).
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| Q |] .
             apply weakening;solveSignature1.
             solveLL.
            
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin IMP P Q |)
           :: (a, d| P |) :: (loc, u| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin IMP P Q |)
           :: (a, d| P |) :: (loc, u| Q |) :: (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin IMP P Q |)
           :: (a, d| P |) :: (loc, u| Q |) :: (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             apply contractionN in H6;solveSignature1...
             apply H in H6...
             
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin IMP P Q |)
           :: (a, d| P |) :: (loc, u| Q |) :: (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.            

Theorem InvIMPL:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
   mt a = true ->
   m4 a = true ->
    seqN (LJ a) n ((a,d| t_bin IMP P Q|) :: (a,d| Q| )::B) M (UP []) -> seq (LJ a) ( (a,d| Q| ):: B) M (UP []).
      Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB Hta H4a HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       
       apply InUNotPos in H6...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
             
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H7...
               checkPermutationCases H5.
               checkPermutationCases H5.
               rewrite H5 in H4.
               LLrew1 H4 H13.
               apply H in H13...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
            simpl... createWorld; solveSignature1.
             rewrite <- H5 in H4.
             apply GenK4RelUT' with (C4:= x) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
             
             rewrite H4 in H9. solveSE.
             rewrite H4 in H10. solveSE.
             rewrite H4 in H11. solveLT.
             rewrite <- H7...
             rewrite H5...
             rewrite <- H5 in H13. 
             simpl...
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. 
             
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin IMP P Q |) :: (a, d| Q |) :: x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H13;solveSignature1.
           
            LLExact H13. rewrite H4...
            apply H in Hyp...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
            simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| Q |) :: x) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
                        
             rewrite H4 in H9.
             apply Forall_cons...
             inversion H9... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             inversion H10... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             inversion H11... 
             rewrite <- H7...
             simpl...
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. 
             checkPermutationCases H5.
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
               rewrite <- H7...         
               rewrite H5...
              apply seqNtoSeq in H13.           
               simpl...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
               rewrite <- H7...         
               rewrite H5...
              apply seqNtoSeq in H13.           
               simpl... }
             
             simpl in H9.
             checkPermutationCases H9.
             apply FocusingBangPar in H7...
             checkPermutationCases H9.
            checkPermutationCases H9.
               rewrite H9 in H7.
               LLrew1 H7 H15.
               apply H in H15...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor. 
            simpl... init2 x0 x2.
            simpl... createWorld; solveSignature1.
             rewrite <- H9 in H7.
             apply GenK4RelUT' with (C4:= x) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
             
             rewrite H7 in H11. solveSE.
             rewrite H7 in H12. solveSE.
             rewrite H7 in H13. solveLT.
             rewrite <- H10...
             rewrite H9...
             rewrite <- H9 in H15. 
             simpl...
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. 
             
             assert(Hyp : seqN (LJ a) x3
        ((a, d| t_bin IMP P Q |) :: (a, d| Q |) :: x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H15;solveSignature1.
           
            LLExact H15. rewrite H7...
            apply H in Hyp...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor.
            simpl... init2 x0 x2.
            simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| Q |) :: x) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
                        
             rewrite H7 in H11.
             apply Forall_cons...
             inversion H11... 
             
             rewrite H7 in H12.
             apply Forall_cons...
             inversion H12... 
             
             rewrite H7 in H13.
             apply Forall_cons...
             reflexivity.
             inversion H13... 
             rewrite <- H10...
             simpl...
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. 
             checkPermutationCases H9.
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor. 
               simpl... init2 x0 x2.
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x4) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
               rewrite <- H10...         
               rewrite H9...
              apply seqNtoSeq in H15.           
               simpl...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               simpl... init2 x0 x2.
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x4) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
               rewrite <- H10...         
               rewrite H9...
              apply seqNtoSeq in H15.           
               simpl...
            - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
            
             { 
             clear H8.
             apply FocusingTensor in H7...
             apply H in H7, H10...
             rewrite H8.
             assert(isFx2:  IsPositiveAtomFormulaL x2).
             OLSolve.
             specialize (posDestruct' isFx2) as HC...
             refine (LinearToClassic2 _ _ _ (LJHasPos a)  (LJHasNeg a) _ H3 _ )... 
             apply weakeningGen...
     apply weakeningGen...
            apply AbsorptionC'...
            solveSignature1.
             }
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
          - checkPermutationCases H6.
             TFocus (BinBipole (IMP_BODY a) Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [u| t_bin IMP P Q |] (@nil oo).
             simpl... createWorld;solveSignature1.
             copyK4 a (d|Q |) B.
             reflexivity.
             finishExp.  rewrite plustpropT...
             LLPar. do 2 LLStore.
             TFocus (POS P a).
             apply ooth_posC... inversion H3.
             LLTensor [d| P |] [u| Q |].
             simpl... solveLL. 
             apply weakening;solveSignature1...
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| Q |]  (@nil oo) .
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |]  (@nil oo)  .
             solveLL.
             TFocus (RINIT OO).
             LLTensor [u| OO |]  (@nil oo)  .
             apply weakening;solveSignature1.
             solveLL.
               
           - checkPermutationCases H6.
              checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor  (@nil oo)  [d| OO |] .
             apply weakening;solveSignature1.
             LLrew2 H6. 
             init2 x x2.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H6.
             
             TFocus (BinBipole (IMP_BODY a) Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
              LLrew2 H6. 
             init2 x0 x.
             simpl...
             createWorld;solveSignature1.
             copyK4 a (d|Q |) B.
             reflexivity.
             finishExp.  rewrite plustpropT...
              LLPar. do 2 LLStore.
              TFocus (POS P a).
             apply ooth_posC... inversion H3.
             LLTensor [d| P |] [u| Q |].
             simpl... solveLL. 
             apply weakening;solveSignature1...
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| Q |]  (@nil oo) .
             solveLL.
             checkPermutationCases H6.
               checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor. 
             apply weakening;solveSignature1.
             solveLL.
             solveLL.
             apply weakening;solveSignature1.
             TFocus (RINIT OO).
             LLTensor. 
             solveLL. solveLL.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin IMP P Q |)
           :: (a, d| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
                 apply FocusingQuest in H6...
         
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin IMP P Q |)
           :: (a, d| Q |) ::  (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin IMP P Q |)
           :: (a, d| Q |) ::  (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin IMP P Q |)
           :: (a, d| Q |) ::  (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.
 
 Theorem InvANDL:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
   mt a = true ->
   m4 a = true ->
    seqN (LJ a) n ((a,d| t_bin AND P Q|) :: (a,d| P| )::(a,d| Q|) :: B) M (UP []) -> seq (LJ a) ((a,d| P| )::(a,d| Q|) :: B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB Hta H4a HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       inversion H6...
       contradict H3.
       constructor.
       apply InUNotPos in H7...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H7...
            apply AbsorptionC'...
            solveSignature1.
            LLSwap.
            apply AbsorptionC'...
            solveSignature1.
            LLSwap;auto.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H7...
               checkPermutationCases H5.
               2:{ 
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
              apply seqNtoSeq in H13.           
              simpl... }
             
             checkPermutationCases H5.
             checkPermutationCases H7.
             rewrite H7 in H5.
             rewrite H5 in H4.
             LLrew1 H4 H13.
             apply H in H13...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x4) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
             
             rewrite H4 in H9. solveSE. 
             rewrite H4 in H10. solveSE.
             rewrite H4 in H11. solveLT. 
             rewrite <- H8...
             
             2:{
             symmetry in H8.
             srewrite H8 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             rewrite H5 in H4.
             LLrew1 H4 H13.
             
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x0)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H13;solveSignature1.
           
            LLExact H13.
            apply H in Hyp...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
            simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x0) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
                        
             rewrite H4 in H9.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H9... 
             inversion H15... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H10... 
             inversion H15... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H11... 
             inversion H15...
              
             rewrite <- H8...
             
             2:{
             symmetry in H8.
             srewrite H8 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             checkPermutationCases H7.
             
             rewrite H7 in H4.
             LLrew1 H4 H13.
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x4)
        [u| G |; d| F0 |] (UP [])).
            apply weakeningN with (F:=  (a, d| P |)) in H13;solveSignature1...
             LLExact H13.
             apply H in Hyp...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x4) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
             
             rewrite H4 in H9.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H9... 
             inversion H15... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H10... 
             inversion H15... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H11... 
             inversion H15...
              
             rewrite <- H8...
             
             2:{
             symmetry in H8.
             srewrite H8 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             LLrew1 H4 H13.
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x)
        [u| G |; d| F0 |] (UP [])).
             apply weakeningN with (F:=(a, d| Q |)) in H13;solveSignature1.
        apply weakeningN with (F:=(a, d| P |)) in H13;solveSignature1.
        LLExact H13.
        apply H in Hyp...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
                        
             rewrite H4 in H9.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H9... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H10... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H11... 
              
             rewrite <- H8...
             
             2:{
             symmetry in H8.
             srewrite H8 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl... }
            { checkPermutationCases H9.
               checkPermutationCases H4.
               checkPermutationCases H9.
            
               apply FocusingBangPar in H7...
              checkPermutationCases H11.
               
            
               2:{ 
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               apply weakening;solveSignature1.
               apply weakening;solveSignature1.
               LLrew2 H10.
               init2 x0 x4. 
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x6) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
              apply seqNtoSeq in H17.           
              simpl... }
             
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               apply weakening;solveSignature1.
               apply weakening;solveSignature1.
               LLrew2 H10.
               init2 x0 x4. 
               simpl... createWorld;solveSignature1.
               
             checkPermutationCases H11.
             checkPermutationCases H12.
             rewrite H12 in H11.
             rewrite H11 in H7.
             LLrew1 H7 H17.
             apply H in H17...
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x9) 
                        (CK:=[])
                        (CN:=x7);solveSignature1...
             
             rewrite H7 in H13. solveSE. 
             rewrite H7 in H14. solveSE.
             rewrite H7 in H15. solveLT. 
             rewrite <- H16...
             
             2:{
             symmetry in H16.
             srewrite H16 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             rewrite H11 in H7.
             LLrew1 H7 H17.
             
             assert(Hyp : seqN (LJ a) x5
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x8)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H17;solveSignature1.
           
            LLExact H17.
            apply H in Hyp...
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x8) 
                        (CK:=[])
                        (CN:=x9);solveSignature1...
             
             rewrite H7 in H13.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H13... 
             inversion H20... 
             
             rewrite H7 in H14.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H14... 
             inversion H20... 
             
             rewrite H7 in H15.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H15... 
             inversion H20...
              
             rewrite <- H16...
             
             2:{
             symmetry in H16.
             srewrite H16 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             checkPermutationCases H12.
             rewrite H12 in H7.
             LLrew1 H7 H17.
             
             assert(Hyp : seqN (LJ a) x5
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x9)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| P |)) in H17;solveSignature1.
           
            LLExact H17.
            apply H in Hyp...
             apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x9) 
                        (CK:=[])
                        (CN:=x8);solveSignature1...
             
             rewrite H7 in H13.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H13... 
             inversion H20... 
             
             rewrite H7 in H14.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H14... 
             inversion H20... 
             
             rewrite H7 in H15.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H15... 
             inversion H20...
              
             rewrite <- H16...
             
             2:{
             symmetry in H16.
             srewrite H16 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
         
             LLrew1 H7 H17.
             assert(Hyp : seqN (LJ a) x5
        ((a, d| t_bin AND P Q |) :: (a, d| P |) ::  (a, d| Q |) :: x)
        [u| G |; d| F0 |] (UP [])).
             apply weakeningN with (F:=(a, d| Q |)) in H17;solveSignature1.
        apply weakeningN with (F:=(a, d| P |)) in H17;solveSignature1.
        LLExact H17.
        apply H in Hyp...
        apply GenK4RelUT' with (C4:= (a, d| P |) :: (a, d| Q |) ::x) 
                        (CK:=[])
                        (CN:=x9);solveSignature1...
             rewrite H7 in H13.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H13... 
             
             rewrite H7 in H14.
             apply Forall_cons...
             apply Forall_cons... 
             inversion H14... 
             
             rewrite H7 in H15.
             apply Forall_cons...
             reflexivity.
             apply Forall_cons...
             reflexivity. 
             inversion H15... 
              
             rewrite <- H16...
             
             2:{
             symmetry in H16.
             srewrite H16 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl... }
           - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H6.
             TFocus (BinBipole AND_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [u| t_bin AND P Q |] (@nil oo).
             simpl... LLRelease. LLWith;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| P |] (@nil oo).
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| Q |] (@nil oo).
             apply weakening;solveSignature1.
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             solveLL.
             checkPermutationCases H6.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             apply weakening;solveSignature1.
             solveLL.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             apply weakening;solveSignature1.
              apply weakening;solveSignature1.
             solveLL.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H6.
             TFocus (RINIT OO).
             LLTensor (@nil oo) [ d| OO |] .
             apply weakening;solveSignature1.
              apply weakening;solveSignature1.
             solveLL.
           - checkPermutationCases H6.
             checkPermutationCases H6.
             checkPermutationCases H9.
             checkPermutationCases H4.
             TFocus (BinBipole AND_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H10. 
             init2 x0 x5.
             simpl... LLRelease. LLWith;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| P |] (@nil oo).
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| Q |] (@nil oo).
             apply weakening;solveSignature1.
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor.
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H10. 
             init2 x0 x5.
             
             solveLL.
             checkPermutationCases H12.
             TFocus (RINIT OO).
             LLTensor.
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H10. 
             init2 x0 x5.
             apply weakening;solveSignature1.
             solveLL.
             TFocus (RINIT OO).
             LLTensor. 
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H10. 
              init2 x0 x5.
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H13. 
             init2 x x8.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin AND P Q |)
           :: (a, d| P |) :: (a, d| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin AND P Q |)
           :: (a, d| P |) :: (a, d| Q |) :: (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin AND P Q |)
           :: (a, d| P |) :: (a, d| Q |) :: (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             checkPermutationCases H4.
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x5
       ((a, d| t_bin AND P Q |)
           :: (a, d| P |) :: (a, d| Q |) :: (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H10.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             apply weakening;solveSignature1...
              apply weakening;solveSignature1...
             LLrew2 H9. 
             init2 x0 x4.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.            

 Theorem InvORR:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
    seqN (LJ a) n ((loc,u| t_bin OR P Q|) :: (loc,u| P| )::(loc,u| Q|) :: B) M (UP []) -> seq (LJ a) ((loc,u| P| )::(loc,u| Q|) :: B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       inversion H6...
       contradict H3.
       constructor.
       apply InUNotPos in H7...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H7...
            apply AbsorptionC'...
            solveSignature1.
            LLSwap.
            apply AbsorptionC'...
            solveSignature1.
            LLSwap;auto.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H9...
               checkPermutationCases H8.
               rewrite H7 in H11.
               inversion H11...
               solveSignature1.
               
               checkPermutationCases H8.
               rewrite H8 in H11.
               inversion H11...
               solveSignature1.
               
               checkPermutationCases H9.
               rewrite H9 in H11.
               inversion H11...
               solveSignature1.
               
               apply weakening;solveSignature1.
               apply weakening;solveSignature1.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
              apply seqNtoSeq in H15.           
              simpl... }
             
              apply FocusingBangPar in H9...
               checkPermutationCases H9.
               rewrite H7 in H12.
               inversion H12...
               solveSignature1.
              checkPermutationCases H9.
               rewrite H9 in H12.
               inversion H12...
               solveSignature1.
              checkPermutationCases H10.
               rewrite H10 in H12.
               inversion H12...
               solveSignature1.
              
               checkPermutationCases H11.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor. 
               LLrew2 H11. 
                init2 x0 x7.
               apply weakening;solveSignature1.
               apply weakening;solveSignature1.
             
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x3) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
              apply seqNtoSeq in H16.           
              simpl...
           - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H6.
              checkPermutationCases H4.
              checkPermutationCases H6.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             apply weakening;solveSignature1.
             apply weakening;solveSignature1. 
             LLrew2 H8. 
             init2 x x3.
           - checkPermutationCases H6.
             TFocus (BinBipole OR_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [d| t_bin OR P Q |] (@nil oo).
             simpl... LLRelease. LLWith;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor  (@nil oo) [ d| P |].
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor  (@nil oo) [ d| Q |].
             apply weakening;solveSignature1.
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor ( @nil oo)[ d| OO |] .
             solveLL.
             checkPermutationCases H6.
             TFocus (RINIT OO).
             LLTensor (@nil oo) [ d| OO |] .
             apply weakening;solveSignature1.
             solveLL.
             TFocus (RINIT OO).
             LLTensor (@nil oo) [d| OO |] .
             apply weakening;solveSignature1.
              apply weakening;solveSignature1.
             solveLL.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H4.
             checkPermutationCases H8.
             
             TFocus (BinBipole OR_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
             apply weakening;solveSignature1.
              LLrew2 H10. 
             init2 x x4.
             simpl... LLRelease. LLWith;LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| P |] .
             solveLL.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| Q |].
             apply weakening;solveSignature1.
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin OR P Q |)
           :: (loc, u| P |) :: (loc, u| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin OR P Q |)
           :: (loc, u| P |) :: (loc, u| Q |) :: (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin OR P Q |)
           :: (loc, u| P |) :: (loc, u| Q |) :: (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
             
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin OR P Q |)
           :: (loc, u| P |) :: (loc, u| Q |) :: (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.  

 Theorem InvORL1:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
   mt a = true ->
   m4 a =  true ->
    seqN (LJ a) n ((a,d| t_bin OR P Q|) :: (a,d| P| )::B) M (UP []) -> seq (LJ a) ((a,d| P| )::B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB Hta H4a HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       apply InUNotPos in H6...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
              {
             apply FocusingWith in H7...
             apply H in H9, H10...
            apply AbsorptionC'...
            solveSignature1. }
             
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H7...
               checkPermutationCases H5.
               2:{ 
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
              apply seqNtoSeq in H13.           
              simpl... }
             
             checkPermutationCases H5.
             rewrite H5 in H4.
             LLrew1 H4 H13.
             apply H in H13...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) ::x0) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
             
             rewrite H4 in H9. solveSE. 
             rewrite H4 in H10. solveSE.
             rewrite H4 in H11. solveLT. 
             rewrite <- H7...
             
             2:{
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             LLrew1 H4 H13.
             
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin OR P Q |) :: (a, d| P |) :: x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| P |)) in H13;solveSignature1.
           
            LLExact H13.
            apply H in Hyp...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
            simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| P |) :: x) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
                        
             rewrite H4 in H9.
             apply Forall_cons...
             inversion H9... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             inversion H10... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             inversion H11... 
              
             rewrite <- H7...
             
             2:{
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...  }
             
             checkPermutationCases H9.
             apply FocusingBangPar in H7...
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               LLrew2 H4.
               init2 x0 x2. 
               simpl... createWorld;solveSignature1.
               
             checkPermutationCases H9.
             checkPermutationCases H9.
             rewrite H9 in H7.
             LLrew1 H7 H15.
             apply H in H15...
             apply GenK4RelUT' with (C4:= (a, d| P |)::x6) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
             
             rewrite H7 in H11. solveSE. 
             rewrite H7 in H12. solveSE.
             rewrite H7 in H13. solveLT. 
             rewrite <- H10...
             
             2:{
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             LLrew1 H7 H15.
             
             assert(Hyp : seqN (LJ a) x3
        ((a, d| t_bin OR P Q |) :: (a, d| P |) ::  x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| P |)) in H15;solveSignature1.
           
            LLExact H15.
            apply H in Hyp...
             apply GenK4RelUT' with (C4:= (a, d| P |) ::x) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
             
             rewrite H7 in H11.
             apply Forall_cons...
             inversion H11... 
             
             rewrite H7 in H12.
             apply Forall_cons...
             inversion H12... 
             
             rewrite H7 in H13.
             apply Forall_cons...
             reflexivity.
             inversion H13... 
              
             rewrite <- H10...
             
             2:{
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             checkPermutationCases H9.
             LLrew1 H9 H15.
             
             apply GenK4RelUT' with (C4:= (a, d| P |) :: x6) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             
                rewrite H9 in H11. solveSE. 
             rewrite H9 in H12. solveSE.
             rewrite H9 in H13. solveLT. 
             rewrite <- H10...
             apply seqNtoSeq in H15.
             simpl...
             apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:= (a, d| P |) :: x6);solveSignature1...
             rewrite <- H10...
             apply seqNtoSeq in H15.
             simpl...
            - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
          - checkPermutationCases H6.
             TFocus (BinBipole OR_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [u| t_bin OR P Q |] (@nil oo).
             simpl... LLPlusL. LLRelease. LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| P |]  (@nil oo) .
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |]  (@nil oo)  .
             solveLL.
             TFocus (RINIT OO).
             LLTensor [u| OO |]  (@nil oo)  .
             apply weakening;solveSignature1.
             solveLL.
               
           - checkPermutationCases H6.
              checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor  (@nil oo)  [d| OO |] .
             apply weakening;solveSignature1.
             LLrew2 H6. 
             init2 x x2.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H6.
             
             TFocus (BinBipole OR_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
              LLrew2 H6. 
             init2 x0 x.
             simpl... LLPlusL. LLRelease. LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor [u| P |]  (@nil oo)  .
             solveLL.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin OR P Q |)
           :: (a, d| P |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
                 apply FocusingQuest in H6...
         
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin OR P Q |)
           :: (a, d| P |) ::  (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin OR P Q |)
           :: (a, d| P |) ::  (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin OR P Q |)
           :: (a, d| P |) ::  (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.
 
 Theorem InvORL2:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
   mt a = true ->
   m4 a =  true ->
    seqN (LJ a) n ((a,d| t_bin OR P Q|) :: (a,d| Q| )::B) M (UP []) -> seq (LJ a) ((a,d| Q| )::B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB Hta H4a HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       apply InUNotPos in H6...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
              {
             apply FocusingWith in H7...
             apply H in H9, H10...
            apply AbsorptionC'...
            solveSignature1. }
             
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H7...
               checkPermutationCases H5.
               2:{ 
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
              apply seqNtoSeq in H13.           
              simpl... }
             
             checkPermutationCases H5.
             rewrite H5 in H4.
             LLrew1 H4 H13.
             apply H in H13...
             TFocus (BinBipole (IMP_BODY a) Right F0 G).
             LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
             simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| Q |) ::x0) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
             
             rewrite H4 in H9. solveSE. 
             rewrite H4 in H10. solveSE.
             rewrite H4 in H11. solveLT. 
             rewrite <- H7...
             
             2:{
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             LLrew1 H4 H13.
             
             assert(Hyp : seqN (LJ a) x1
        ((a, d| t_bin OR P Q |) :: (a, d| Q |) :: x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H13;solveSignature1.
           
            LLExact H13.
            apply H in Hyp...
            TFocus (BinBipole (IMP_BODY a) Right F0 G).
            LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
            simpl... createWorld; solveSignature1.
             apply GenK4RelUT' with (C4:= (a, d| Q |) :: x) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
                        
             rewrite H4 in H9.
             apply Forall_cons...
             inversion H9... 
             
             rewrite H4 in H10.
             apply Forall_cons...
             inversion H10... 
             
             rewrite H4 in H11.
             apply Forall_cons...
             reflexivity.
             inversion H11... 
              
             rewrite <- H7...
             
             2:{
             symmetry in H7.
             srewrite H7 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...  }
             
             checkPermutationCases H9.
             apply FocusingBangPar in H7...
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor.
               LLrew2 H4.
               init2 x0 x2. 
               simpl... createWorld;solveSignature1.
               
             checkPermutationCases H9.
             checkPermutationCases H9.
             rewrite H9 in H7.
             LLrew1 H7 H15.
             apply H in H15...
             apply GenK4RelUT' with (C4:= (a, d| Q |)::x6) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
             
             rewrite H7 in H11. solveSE. 
             rewrite H7 in H12. solveSE.
             rewrite H7 in H13. solveLT. 
             rewrite <- H10...
             
             2:{
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             LLrew1 H7 H15.
             
             assert(Hyp : seqN (LJ a) x3
        ((a, d| t_bin OR P Q |) :: (a, d| Q |) ::  x)
        [u| G |; d| F0 |] (UP [])).
        eapply weakeningN with (F:=(a, d| Q |)) in H15;solveSignature1.
           
            LLExact H15.
            apply H in Hyp...
             apply GenK4RelUT' with (C4:= (a, d| Q |) ::x) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
             
             rewrite H7 in H11.
             apply Forall_cons...
             inversion H11... 
             
             rewrite H7 in H12.
             apply Forall_cons...
             inversion H12... 
             
             rewrite H7 in H13.
             apply Forall_cons...
             reflexivity.
             inversion H13... 
              
             rewrite <- H10...
             
             2:{
             symmetry in H10.
             srewrite H10 in isFB.
             rewrite map_app in isFB. OLSolve. }
             simpl...
             
             checkPermutationCases H9.
             LLrew1 H9 H15.
             
             apply GenK4RelUT' with (C4:= (a, d| Q |) :: x6) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
             
                rewrite H9 in H11. solveSE. 
             rewrite H9 in H12. solveSE.
             rewrite H9 in H13. solveLT. 
             rewrite <- H10...
             apply seqNtoSeq in H15.
             simpl...
             apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:= (a, d| Q |) :: x6);solveSignature1...
             rewrite <- H10...
             apply seqNtoSeq in H15.
             simpl...
            - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
          - checkPermutationCases H6.
             TFocus (BinBipole OR_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [u| t_bin OR P Q |] (@nil oo).
             simpl... LLPlusR. LLRelease. LLStore.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [ u| Q |]  (@nil oo) .
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |]  (@nil oo)  .
             solveLL.
             TFocus (RINIT OO).
             LLTensor [u| OO |]  (@nil oo)  .
             apply weakening;solveSignature1.
             solveLL.
               
           - checkPermutationCases H6.
              checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor  (@nil oo)  [d| OO |] .
             apply weakening;solveSignature1.
             LLrew2 H6. 
             init2 x x2.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H6.
             
             TFocus (BinBipole OR_BODY Right P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
              LLrew2 H6. 
             init2 x0 x.
             simpl... LLPlusR. LLRelease. LLStore.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor [u| Q |]  (@nil oo)  .
             solveLL.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin OR P Q |)
           :: (a, d| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
                 apply FocusingQuest in H6...
         
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin OR P Q |)
           :: (a, d| Q |) ::  (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((a, d| t_bin OR P Q |)
           :: (a, d| Q |) ::  (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((a, d| t_bin OR P Q |)
           :: (a, d| Q |) ::  (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed. 

 Theorem InvANDR1:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
    seqN (LJ a) n ((loc,u| t_bin AND P Q|) :: (loc,u| P| )::B) M (UP []) -> seq (LJ a) ((loc,u| P| )::B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       apply InUNotPos in H6...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
            {
             apply FocusingWith in H7...
             apply H in H9, H10...
            apply AbsorptionC'...
            solveSignature1. }
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H9...
               checkPermutationCases H8.
               rewrite H7 in H11.
               inversion H11...
               solveSignature1.
               
               checkPermutationCases H8.
               rewrite H8 in H11.
               inversion H11...
               solveSignature1.
               
               apply weakening;solveSignature1.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
              apply seqNtoSeq in H15.           
              simpl... }
             
              apply FocusingBangPar in H9...
               checkPermutationCases H9.
               rewrite H7 in H12.
               inversion H12...
               solveSignature1.
              checkPermutationCases H9.
               rewrite H9 in H12.
               inversion H12...
               solveSignature1.
               checkPermutationCases H11.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor. 
               LLrew2 H11. 
                init2 x0 x6.
               apply weakening;solveSignature1.
             
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x3) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
              apply seqNtoSeq in H16.           
              simpl...
           - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H6.
              checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             apply weakening;solveSignature1.
             LLrew2 H6. 
             init2 x x2.
           - checkPermutationCases H6.
             TFocus (BinBipole AND_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [d| t_bin AND P Q |] (@nil oo).
             simpl... LLPlusL. LLRelease. LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor  (@nil oo) [ d| P |].
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor ( @nil oo)[ d| OO |] .
             solveLL.
             TFocus (RINIT OO).
             LLTensor (@nil oo) [ d| OO |] .
             apply weakening;solveSignature1.
             solveLL.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H4.
             
             TFocus (BinBipole AND_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
              LLrew2 H8. 
             init2 x x3.
             simpl... LLPlusL. LLRelease. LLStore.
             TFocus (RINIT P).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| P |] .
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| P |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| P |) ::  (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| P |) ::  (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
             
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| P |) ::  (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.
 
 Theorem InvANDR2:  forall n a P Q B M, 
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second B) ->
    seqN (LJ a) n ((loc,u| t_bin AND P Q|) :: (loc,u| Q| )::B) M (UP []) -> seq (LJ a) ((loc,u| Q| )::B) M (UP []).
    Proof with sauto;OLSolve.
      induction n using strongind;intros *;
      intros isFM isFB HF.
      inversion HF...
      inversion HF...
      apply RemoveNotPos1 in H2...
       intro Hc. inversion Hc;inversion H1...
       inversion H4...
       contradict H3.
       constructor.
       inversion H0...
       contradict H3.
       constructor.
       apply InUNotPos in H6...
       rewrite allU in H1...
       2:{ solveSignature1. }
       inversion H1...
       + inversion H0...
           - apply BipoleReasoning in H3...
             TFocus (CteBipole TT_BODY Right).
             LLTensor [u| t_cons TT | ] x0.
             simpl... 
             simpl in H9.
             checkPermutationCases H9.
             TFocus (CteBipole TT_BODY Right).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             inversion H7...
             solveF.
             inversion H7...
             solveF.
           - apply BipoleReasoning in H3...
             TFocus (CteBipole FF_BODY Left).
             LLTensor [d| t_cons FF | ] x0.
             simpl... 
             checkPermutationCases H9.
             TFocus (CteBipole FF_BODY Left).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
       + inversion H0...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole AND_BODY Right F0 G).
              LLTensor [u| t_bin AND F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.
            {
             apply FocusingWith in H7...
             apply H in H9, H10...
            apply AbsorptionC'...
            solveSignature1. }
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole AND_BODY Right F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2: LLTensor [d| t_bin AND F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole AND_BODY Left F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
          - apply BipoleReasoning in H3...
            apply FocusingPlus in H7...
            1,2: apply H in H6...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2: LLTensor [u| t_bin OR F0 G| ] x0.
            1,2: simpl...
            
            checkPermutationCases H9.
            apply FocusingPlus in H7...
            1,2: apply H in H9...
            1,2: TFocus (BinBipole OR_BODY Right F0 G).
            1,2:LLTensor (@nil oo) M.
            1,3: LLrew2 H5. 
            1,2: init2 x0 x2.
            1,2: simpl...
           - apply BipoleReasoning in H3...
              apply FocusingWith in H7...
              apply H in H7, H9...
              TFocus (BinBipole OR_BODY Left F0 G).
              LLTensor [d| t_bin OR F0 G| ] x0. 
             simpl...
             checkPermutationCases H9.  
             apply FocusingWith in H7...
             apply H in H10, H11...
             TFocus (BinBipole OR_BODY Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             simpl...
          - apply BipoleReasoning in H3...
            { apply FocusingBangPar in H9...
               checkPermutationCases H8.
               rewrite H7 in H11.
               inversion H11...
               solveSignature1.
               
               checkPermutationCases H8.
               rewrite H8 in H11.
               inversion H11...
               solveSignature1.
               
               apply weakening;solveSignature1.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor [u| t_bin IMP F0 G| ] (@nil oo).
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x2) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
              apply seqNtoSeq in H15.           
              simpl... }
             
              apply FocusingBangPar in H9...
               checkPermutationCases H9.
               rewrite H7 in H12.
               inversion H12...
               solveSignature1.
              checkPermutationCases H9.
               rewrite H9 in H12.
               inversion H12...
               solveSignature1.
               checkPermutationCases H11.
               
               TFocus (BinBipole (IMP_BODY a) Right F0 G).
               LLTensor. 
               LLrew2 H11. 
                init2 x0 x6.
               apply weakening;solveSignature1.
             
               simpl... createWorld;solveSignature1.
               apply GenK4RelUT' with (C4:=x3) 
                        (CK:=[])
                        (CN:=x5);solveSignature1...
              apply seqNtoSeq in H16.           
              simpl...
           - apply BipoleReasoning in H3...
             apply FocusingTensor in H7...
             apply H in H6, H10...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor [d| t_bin IMP F0 G| ] x0.
             simpl...
             LLTensor x2 x3.
             1-2: rewrite H7 in H8.
             1-2: rewrite H8 in isFM.
             1-2: inversion isFM...
             
             checkPermutationCases H9.
             apply FocusingTensor in H7...
             apply H in H9, H12...
             TFocus (BinBipole (IMP_BODY a) Left F0 G).
             LLTensor (@nil oo) M.
             LLrew2 H5. 
             init2 x0 x2.
             LLTensor x4 x5.
       + apply FocusingInitRuleU in H3... 
           - TFocus (RINIT OO).
              LLTensor [u| OO |] [d| OO |].
           - checkPermutationCases H6.
              checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor [ u| OO |] (@nil oo).
             apply weakening;solveSignature1.
             LLrew2 H6. 
             init2 x x2.
           - checkPermutationCases H6.
             TFocus (BinBipole AND_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor [d| t_bin AND P Q |] (@nil oo).
             simpl... LLPlusR. LLRelease. LLStore.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor  (@nil oo) [ d| Q |].
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor ( @nil oo)[ d| OO |] .
             solveLL.
             TFocus (RINIT OO).
             LLTensor (@nil oo) [ d| OO |] .
             apply weakening;solveSignature1.
             solveLL.
           - checkPermutationCases H6.
             checkPermutationCases H4.
             checkPermutationCases H4.
             
             TFocus (BinBipole AND_BODY Left P Q).
             apply ooth_rulesC.
             constructor...
             inversion H3.
             LLTensor.
             apply weakening;solveSignature1.
              LLrew2 H8. 
             init2 x x3.
             simpl... LLPlusR. LLRelease. LLStore.
             TFocus (RINIT Q).
             apply ooth_initC...
             inversion H3.
             LLTensor (@nil oo) [ d| Q |] .
             solveLL.
             checkPermutationCases H4.
             TFocus (RINIT OO).
             LLTensor.
              LLrew2 H6. 
             init2 x0 x3.
              LLrew2 H4. 
             init2 x x4.
           +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| Q |) :: (a, d| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor [d| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| Q |) ::  (a, d| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (POS OO a).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
       +   apply BipoleReasoning in H3...
             apply FocusingQuest in H6...
             assert(Hyp: seqN (LJ a) x1
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| Q |) ::  (loc, u| OO |)
        :: B) x0 
       (UP [])).
             LLExact H5.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor [u| OO| ] x0.
             LLRelease. LLStoreC.
             LLExact Hyp.
             
             checkPermutationCases H8.
             apply FocusingQuest in H6...
             eapply contractionN in H6...
             apply H in H6...
             solveSignature1.
             
             apply FocusingQuest in H6...
             
             assert(Hyp: seqN (LJ a) x3
       ((loc, u| t_bin AND P Q |)
           :: (loc, u| Q |) ::  (loc, u| OO |)
        :: B) M 
       (UP [])).
             LLExact H8.
             apply H in Hyp...
             TFocus (NEG OO loc).
             LLTensor (@nil oo) M . 
             LLrew2 H4. 
             init2 x0 x2.
             LLRelease. LLStoreC.
             LLExact Hyp.
 Qed.
 
 
Theorem InversionTT
     : forall (n m: nat) (a : subexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       seqN (LJ a) m ((a, d| t_cons TT |) :: B) M (UP []) ->
       seq (LJC a n) B M (UP []).
 Proof with auto.
   intros. 
   apply InvTT in H1...
   refine (WeakTheory _ _ H1)...
   apply TheoryEmb1.
 Qed.   

Theorem InversionFF
     : forall (n m: nat) (a : subexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       seqN (LJ a) m ((loc, u| t_cons FF |) :: B) M (UP []) ->
       seq (LJC a n) B M (UP []).
 Proof with auto.
   intros. 
   apply InvFF in H1...
   refine (WeakTheory _ _ H1)...
   apply TheoryEmb1.
 Qed.
 
 Theorem InversionANDL
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       mt a = true ->
       m4 a = true ->
       seqN (LJ a) m
         ((a, d| t_bin AND P Q |) :: B) M 
         (UP []) ->
       seq (LJC a n) ((a, d| P |) :: (a, d| Q |) :: B) M
         (UP []).
 Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvANDL with (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1.
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.

  Theorem InversionORR
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       seqN (LJ a) m
         ((loc, u| t_bin OR P Q |) :: B) M 
         (UP []) ->
       seq (LJC a n) ((loc, u| P |) :: (loc, u| Q |) :: B) M
         (UP []).
 Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvORR with (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1.
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.
  
 Theorem InversionANDR1
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       seqN (LJ a) m
         ((loc, u| t_bin AND P Q |) :: B) M
         (UP []) ->
       seq (LJC a n) ((loc, u| P |) :: B) M (UP []).
  Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvANDR1 with (Q:=Q) (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.        

 Theorem InversionANDR2
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       seqN (LJ a) m
         ((loc, u| t_bin AND P Q |) :: B) M
         (UP []) ->
       seq (LJC a n) ((loc, u| Q |) :: B) M (UP []).
  Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvANDR2 with (P:=P) (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.        
 
  Theorem InversionORL1
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       mt a = true ->
       m4 a = true ->
       seqN (LJ a) m
         ((a, d| t_bin OR P Q |) :: B) M
         (UP []) ->
       seq (LJC a n) ((a, d| P |) :: B) M (UP []).
  Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvORL1 with (Q:=Q) (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.        

  Theorem InversionORL2
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       mt a = true ->
       m4 a = true ->
       seqN (LJ a) m
         ((a, d| t_bin OR P Q |) :: B) M
         (UP []) ->
       seq (LJC a n) ((a, d| Q |) :: B) M (UP []).
  Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvORL2 with (P:=P) (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1...
  Qed.
   
  Theorem InversionIMPL
     : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       mt a = true ->
       m4 a = true ->
       seqN (LJ a) m
         ((a, d| t_bin IMP P Q |) :: B) M
         (UP []) -> 
         seq (LJC a n) ((a, d| Q |) :: B) M (UP []).
  Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvIMPL with (P:=P) (n:=m)...
      LLSwap.
   apply weakeningN;solveSignature1...
  Qed.
           
  Theorem InversionIMPR
          : forall (n m: nat) (a : subexp) (P Q : uexp)
         (B : list (subexp * oo)) (M : list oo),
       IsPositiveAtomFormulaL M ->
       IsPositiveAtomFormulaL (second B) ->
       mt a = true ->
       m4 a = true ->
       seqN (LJ a) m
         ((loc, u| t_bin IMP P Q |) :: B) M 
         (UP []) ->
       seq (LJC a n) ((a, d| P |) :: (loc, u| Q |) :: B) M
         (UP []).
Proof with auto.
   intros.
   eapply WeakTheory with (th:=(LJ a)). 
   apply TheoryEmb1.
   eapply InvIMPR with (n:=m)...
   LLSwap.
   apply weakeningN;solveSignature1... 
LLSwap.
   apply weakeningN;solveSignature1...

  Qed.
       
End LJInv.