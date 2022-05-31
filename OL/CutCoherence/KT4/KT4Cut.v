Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.KT4.KT4Bipoles.
Import MMLL.Misc.Permutations.
Require Import MMLL.SL.FLLReasoning.
Require Import MMLL.SL.InvPositivePhase.
         
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section KT4Cut.

Context {SI: Signature}.

 Definition CutC (h: nat) (a:subexp):= forall m n n' i j FC M N L,
    m <= h ->
    m = i + j ->
    n' <= n ->
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL N ->
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second L) ->
    mt a = true ->
    m4 a = true ->
    (seqN (KT4 a) i ((loc,u|FC|)::L) M (UP []) ->
     seqN (KT4 a) j ((loc,d|FC|)::L) N (UP []) -> 
     seq (KT4C a (pred n)) L (M ++ N) (UP [])).
 

Ltac CutTacPOSNEG := sauto;
  try
    match goal with
    | [ |- isFormula _] => constructor;auto
    | [ |- IsPositiveAtomFormula _] =>  constructor;auto
    | [ |- KT4C _ _] => autounfold; solve[constructor;constructor;auto]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
      solve [apply PositiveAtomIn in H';auto;contradiction]
    | [ H: seqN _ _ _ _ (DW zero) |- _] => invTri H
    | [ H: seq  _ _ _ (DW zero) |- _] => invTri' H
    | [ |- KT4C _ _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [ |- KT4 _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [|- IsPositiveAtomFormulaL (d| _ | :: _)] => solve[repeat (constructor;auto)]
    end; OLSolve.

 Ltac solveBipole :=
 match goal with
| [H: context[CteBipole] |- _] => inversion H 
| [H: context[BinBipole] |- _] => inversion H
| [H: context[QuBipole] |- _] => inversion H  end.

Tactic Notation "Bipole"  constr(B) constr(S):=
        match B with 
        | TT => TFocus (CteBipole TT_BODY S)
        | FF => TFocus (CteBipole FF_BODY S)
end.

Tactic Notation "Bipole"  constr(B) constr(S) constr(F) constr(G):= 
     match B with
     | AND => TFocus (BinBipole AND_BODY S F G)
     | OR => TFocus (BinBipole OR_BODY S F G)
  end.
  
  
  Ltac LLSwapL H :=
        let Hs := type of H in 
        match Hs with
        |  (seqN _ _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLCN with (LC':= (G :: F :: L)) in H;[|perm]
        |  (seq  _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLC with (LC':= (G :: F :: L)) in H;[|perm]
        end.

  Ltac LLSwapC H :=
        let Hs := type of H in 
        match Hs with
        |  (seqN _ _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCCN with (CC':= (G :: F :: L)) in H;[|perm]
        |  (seq  _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCC with (CC':= (G :: F :: L)) in H;[|perm]
        end.

Lemma exchangeSwap n th L F A B C: Permutation A (B ::C)
 -> seqN th n L (F :: A) (UP []) -> seqN th n L (B :: F :: C) (UP []).
 Proof with sauto.
 intros.
 eapply exchangeLCN.
 2: exact H0.
 rewrite H...
 Qed.
        
Ltac PermSwap Hs Hp:=
    eapply exchangeSwap in Hs;[| exact Hp].

Lemma exchangeSwap2 n th L F G A B C: Permutation A (B ::C)
 -> seqN th n L (F :: G :: A) (UP []) -> seqN th n L (B :: F :: G :: C) (UP []).
 Proof with sauto.
 intros.
 eapply exchangeLCN.
 2: exact H0.
 rewrite H...
 Qed.
        
Ltac PermSwap2 Hs Hp:=
    eapply exchangeSwap2 in Hs;[| exact Hp].

 

 

Ltac permuteANDR :=              
  match goal with 
  | [ H1 : seqN _ _ _ _ (DW (AND_BODY.(rb_rightBody) _ _)),
       H2 : Permutation ?N (u| t_bin AND ?F ?G | :: ?x) |- 
       seq _ _ (?M ++ ?N) (UP []) ] => 
       
      apply FocusingWith in H1;sauto;
      TFocus (BinBipole AND_BODY Right F G); 
      simpl;
      LLTensor [u| t_bin AND F G | ] (M++x);[
      rewrite H2;sauto  |  
      solveLL;LLStore ; rewrite <- Permutation_midle ]
 
  | [ H1 : seqN _ _ _ _ (DW (AND_BODY.(rb_rightBody) _ _)),
       H2 : Permutation ?M (u| t_bin AND ?F ?G | :: ?x) |- 
       seq _ _ (?M ++ ?N) (UP []) ] => 
       
      apply FocusingWith in H1;sauto;
      TFocus (BinBipole AND_BODY Right F G); 
      simpl;
      LLTensor [u| t_bin AND F G | ] (x++N);[
      rewrite H2;sauto  |  
      solveLL;LLStore  ]   
  end.
  
   
Ltac permuteANDRight :=              
    match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin AND ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole AND_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin AND F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin AND ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole AND_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
  end. 



Ltac permuteANDLeft :=              
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ?N (d| t_bin AND ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin AND F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusL;solveLL;rewrite <- Permutation_midle ]
        | 
         TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin AND F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusR;solveLL;rewrite <- Permutation_midle ]] 
        
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ((?i, d| t_bin AND ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusL;solveLL; rewrite <- Permutation_midle ]
        |
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusR;solveLL; rewrite <- Permutation_midle ]
        ]     
     end. 
        
   Ltac permuteORRight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin OR ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin OR F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusL;solveLL;rewrite <- Permutation_midle ]
        | TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin OR F G | ] (M++x);
        [rewrite Hpp;sauto  | LLPlusR;solveLL;rewrite <- Permutation_midle ]
        ]  
   | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin OR ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusL;solveLL; rewrite <- Permutation_midle ]
        |
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusR;solveLL; rewrite <- Permutation_midle ]
        ]     
     end. 
 
  
 Ltac permuteORLeft :=              
              
                match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ?N (d| t_bin OR ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole OR_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin OR F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
         | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ((?i, d| t_bin OR ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole OR_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
      
            end.
   
  Context  {USI:UnbSignature}.
  Context  {UND:UnbNoDSignature}.
 
  
  Ltac applyCutC Hl Hr :=
 match goal with
  [ C: CutC _ _, 
    Hc: lengthUexp ?P ?n |- seq _ ?L (?M++?N) _  ] =>
    match type of Hl with
      | seqN _ ?l ((?i, u| ?P|)::?L) ?M _  =>
         match type of Hr with
         | seqN _ ?r ((?i, d| ?P|)::?L) ?N _ =>
           let H' := fresh "H" in assert(H' : l + r = l + r) by auto;
           refine(C _ _ _ _ _ _ _ _ _ _ H' _ _ Hc _ _ _ _ _ Hl Hr);
           CutTacPOSNEG
          | _ => idtac "Debug " Hr
          end
     | _ => idtac "Debug " Hl
   end
end.   


    
  Lemma KT4CutC F F0 FC L M N a h n0 n1 n' n:
     m4 a = true -> mt a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutC h a ->
     seqN (KT4 a) (S n0) ((loc,u| FC |) :: L) M (UP []) ->
     seqN (KT4 a) (S n1) ((loc,d| FC |) :: L) N (UP []) ->
     KT4 a F ->
     ~ IsPositiveAtom F ->
     seqN (KT4 a) n0 ((loc,u| FC |) :: L) M (DW F) ->
     KT4 a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (KT4 a) n1 ((loc,d| FC |) :: L) N (DW F0) ->
     seq (KT4C a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros A4 H4 Heqh isFFC lngF HRel isFM isFN isFL. 
    intro CutHC.
    intros Hi Hj.
    intros H H0 H1 H2 H3 H5.

   inversion H;sauto. 
   (* Analizing the derivation on the left *)     
   * (* 1/6 - Constants *)
      inversion H6;sauto.
      (* Four Cases *)     
      3:{ 
      apply BipoleReasoning in H1...
      inversion H10...
      solveF.
      inversion H10...
      solveF. }
    3:{
      apply BipoleReasoning in H1...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (N++x0).
      rewrite H11...
      simpl. solveLL.
      checkPermutationCases H12.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H1...
      inversion H10...
      solveF.
      inversion H10...
      solveF. }
      apply BipoleReasoning in H1...
      simpl in H11.
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (x0++N).
      rewrite H11...
      simpl...
      checkPermutationCases H12.
      clear H11.
      {   (** FF Right is principal *)
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
      3:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H14...
      simpl. solveLL.
      checkPermutationCases H15.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H5...
      inversion H12...
      solveF.
      inversion H12...
      solveF. }
      
      apply BipoleReasoning in H5...
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (M++x1).
      rewrite H7...
      simpl...       
                 checkPermutationCases H11.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDRight.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole AND_BODY Right F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDLeft.
                applyCutC Hi H12.
                applyCutC Hi H12.
                 checkPermutationCases H15.
                apply FocusingPlus in H13...
                all:TFocus (BinBipole AND_BODY Left F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORRight.
                applyCutC Hi H12.
                applyCutC Hi H12.
                 checkPermutationCases H15.
                apply FocusingPlus in H13...
                all:TFocus (BinBipole OR_BODY Right F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.           
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORLeft.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole OR_BODY Left F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll loc...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode loc N ++ (CEncode loc M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H11.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg loc.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
                TFocus (NEG (t_cons TT) loc).
                inversion H5...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Modal Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingBang in H13...
                PosNegAll loc...
               1-2: intro;intros...
                rewrite CEncodeApp...
                rewrite app_assoc_reverse.
                apply weakeningGen...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x3) (CK:=[]) (CN:=(loc, u| t_ucon (BOX_BODY a).(ucon) F |) ::x4)...
                solveSignature1.
                rewrite H13...
                simpl...
                LLStore.
                apply seqNtoSeq in H19.
                refine(WeakTheory _ _ H19).
                apply TheoryEmb1.
               
               checkPermutationCases H15.
               
               apply FocusingBang in H13...
               apply WeakPosNegAll with (a:=loc)...
                1-2: intro;intros...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x5) (CK:=[]) (CN:=x6)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H21.
                refine(WeakTheory _ _ H21).
                apply TheoryEmb1.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor [d| t_ucon (BOX_BODY a).(ucon) F|] (M++x1).       rewrite H14...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H11.
                applyCutC Hi H11.
                apply allU.
                
                checkPermutationCases H15.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor (@nil oo) (M++N). 
                solveLL...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H15.
                applyCutC Hi H15.
                apply allU.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO loc).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            
            checkPermutationCases H14.
            { clear H13. 
               apply FocusingQuest in H12...
               eapply contractionN in H8...
                applyCutC Hi H8.
               apply allU. 
      }
            
            apply FocusingQuest in H12...
           
            TFocus (POS OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.  }
   
    (* Continuing the case 3/4 - FF Right *) 
    
    Bipole TT Right. 
    LLTensor (@nil oo) (M++N).
    solveLL...
    simpl...
     * (* 2/6 - Connectives *)
        inversion H6;sauto. 
      ** (* 1/6 - AND RIGHT *)
      apply BipoleReasoning in H1...
      apply FocusingWith in H10...
      PosNegAll loc...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               solveSignature1.
               rewrite secCEncode.
      TFocus (BinBipole AND_BODY Right F1 G). 
      LLTensor [u| t_bin AND F1 G|] x0.
      simpl. LLRelease. LLWith.
      1-2: LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1,2 : solveSignature1. 
      1-2 : rewrite secCEncode.
      applyCutC H10 Hj.
      applyCutC H12 Hj.
      
      checkPermutationCases H12.
      { (** AND Right is principal *)
          clear H11.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
           3:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H14...
      simpl. solveLL.
      checkPermutationCases H15.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
      
      apply BipoleReasoning in H5...
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (M++x1).
      rewrite H14...
      simpl...       
                 checkPermutationCases H15.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDRight.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole AND_BODY Right F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDLeft.
                applyCutC Hi H12.
                applyCutC Hi H12.
                checkPermutationCases H15.
                 
           { clear H14.
                    
           apply @PosNegSetT' with (a:=loc)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           Import SL.CutElimination.
           
           eapply GeneralCut' with (C:=dual ((AND_BODY.(rb_leftBody) F1 G)))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((AND_BODY.(rb_rightBody) F1 G)))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H5 _)...
           apply weakeningAll...
                    
           apply AND_CUTCOHERENT... 

           simpl.
           apply FocusingWith in H10...
           LLRelease. 
           LLWith. 
           1-2: LLStore.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1,2: solveSignature1.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite app_comm_cons. 
           applyCutC H10 Hj.
           applyCutC H11 Hj. 
           
           simpl.
           apply FocusingWith in H10...
           apply FocusingPlus in H13...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.  
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle.
           1-2: applyCutC Hi H9. }

                apply FocusingPlus in H13...
                all:TFocus (BinBipole AND_BODY Left F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORRight.
                applyCutC Hi H12.
                applyCutC Hi H12.
                 checkPermutationCases H15.
                apply FocusingPlus in H13...
                all:TFocus (BinBipole OR_BODY Right F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.           
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORLeft.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole OR_BODY Left F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll loc...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode loc N ++ (CEncode loc M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
              solveSignature1. 
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H11.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg loc.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
                TFocus (NEG (t_bin AND F1 G) loc).
                inversion H5...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Modal Case *)   
            inversion H1...     
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingBang in H13...
                PosNegAll loc...
               1-2: intro;intros...
                rewrite CEncodeApp...
                rewrite app_assoc_reverse.
                apply weakeningGen...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x3) (CK:=[]) (CN:=(loc, u| t_ucon (BOX_BODY a).(ucon) F |) ::x4)...
                solveSignature1.
                rewrite H13...
                simpl...
                LLStore.
                apply seqNtoSeq in H19.
                refine(WeakTheory _ _ H19).
                apply TheoryEmb1.
               
               checkPermutationCases H15.
               
               apply FocusingBang in H13...
               apply WeakPosNegAll with (a:=loc)...
                1-2: intro;intros...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x5) (CK:=[]) (CN:=x6)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H21.
                refine(WeakTheory _ _ H21).
                apply TheoryEmb1.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor [d| t_ucon (BOX_BODY a).(ucon) F|] (M++x1).       rewrite H14...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H11.
                applyCutC Hi H11.
                apply allU.
                
                checkPermutationCases H15.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor (@nil oo) (M++N). 
                solveLL...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H15.
                applyCutC Hi H15.
                apply allU.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO loc).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            
            checkPermutationCases H14.
                     { clear H13. 
               apply FocusingQuest in H12...
               eapply contractionN in H8...
                applyCutC Hi H8.
               apply allU. 
      }    
            apply FocusingQuest in H12...
           
            TFocus (POS OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.  }
            
      apply FocusingWith in H10...
      TFocus (BinBipole AND_BODY Right F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL...
      LLRelease.
      LLWith. 1-2: LLStore.
      rewrite app_comm_cons.
      applyCutC H13 Hj.
      rewrite app_comm_cons.
      applyCutC H14 Hj.
      
      ** (* 2/6 - AND LEFT *)
      apply BipoleReasoning in H1...
      PosNegAll loc...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               solveSignature1.
               rewrite secCEncode.
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole AND_BODY Left F1 G). 
      1-2: LLTensor [d| t_bin AND F1 G|] x0.
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: solveSignature1.
      1-2 : rewrite secCEncode.
      applyCutC H9 Hj.
      applyCutC H9 Hj.
      
      checkPermutationCases H12.
      
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole AND_BODY Left F1 G). 
      1-2: LLTensor (@nil oo) (M++N).
      1,3: solveLL...
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      rewrite app_comm_cons.
      applyCutC H12 Hj.
      rewrite app_comm_cons.
      applyCutC H12 Hj.
      ** (* 3/6 - OR RIGHT *)
      apply BipoleReasoning in H1...
      PosNegAll loc...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               solveSignature1.
               rewrite secCEncode.
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole OR_BODY Right F1 G). 
      1-2: LLTensor [u| t_bin OR F1 G|] x0.
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: solveSignature1.
      1-2 : rewrite secCEncode.
      applyCutC H9 Hj.
      applyCutC H9 Hj.
      
      checkPermutationCases H12.
      { (** OR Right is principal *)
          clear H11.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
           3:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H14...
      simpl. solveLL.
      checkPermutationCases H15.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
      
      apply BipoleReasoning in H5...
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (M++x1).
      rewrite H14...
      simpl...       
                 checkPermutationCases H15.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
                
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDRight.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole AND_BODY Right F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDLeft.
                applyCutC Hi H12.
                applyCutC Hi H12.
                checkPermutationCases H15.
                 
                apply FocusingPlus in H13...
                all:TFocus (BinBipole AND_BODY Left F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORRight.
                applyCutC Hi H12.
                applyCutC Hi H12.
                 checkPermutationCases H15.
                apply FocusingPlus in H13...
                all:TFocus (BinBipole OR_BODY Right F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.           
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORLeft.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
         { clear H14.
                    
           apply @PosNegSetT' with (a:=loc)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           eapply GeneralCut' with (C:=dual ((OR_BODY.(rb_leftBody) F1 G)))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((OR_BODY.(rb_rightBody) F1 G)))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H5 _)...
           apply weakeningAll...
                    
           apply OR_CUTCOHERENT... 
           
           simpl.
           apply FocusingWith in H13...
           apply FocusingPlus in H10...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.  
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite app_comm_cons. 
           1-2: applyCutC H9 Hj.
           
           simpl.
           apply FocusingWith in H13...
           LLRelease. 
           LLWith. 
           1-2: LLStore.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: solveSignature1.
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle. 
           applyCutC Hi H11.
           applyCutC Hi H13.        }                
        
                apply FocusingWith in H13...
                TFocus (BinBipole OR_BODY Left F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll loc...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode loc N ++ (CEncode loc M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
              solveSignature1. 
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H11.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg loc.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
                TFocus (NEG (t_bin OR F1 G) loc).
                inversion H5...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Modal Case *)   
            inversion H1...     
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingBang in H13...
                PosNegAll loc...
               1-2: intro;intros...
                rewrite CEncodeApp...
                rewrite app_assoc_reverse.
                apply weakeningGen...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x3) (CK:=[]) (CN:=(loc, u| t_ucon (BOX_BODY a).(ucon) F |) ::x4)...
                solveSignature1.
                rewrite H13...
                simpl...
                LLStore.
                apply seqNtoSeq in H19.
                refine(WeakTheory _ _ H19).
                apply TheoryEmb1.
               
               checkPermutationCases H15.
               
               apply FocusingBang in H13...
               apply WeakPosNegAll with (a:=loc)...
                1-2: intro;intros...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x5) (CK:=[]) (CN:=x6)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H21.
                refine(WeakTheory _ _ H21).
                apply TheoryEmb1.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor [d| t_ucon (BOX_BODY a).(ucon) F|] (M++x1).       rewrite H14...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H11.
                applyCutC Hi H11.
                apply allU.
                
                checkPermutationCases H15.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor (@nil oo) (M++N). 
                solveLL...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H15.
                applyCutC Hi H15.
                apply allU.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO loc).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            
            checkPermutationCases H14.
                 { clear H13. 
               apply FocusingQuest in H12...
               eapply contractionN in H8...
                applyCutC Hi H8.
               apply allU. 
      }
            apply FocusingQuest in H12...
           
            TFocus (POS OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.  }
                
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole OR_BODY Right F1 G). 
      1-2: LLTensor (@nil oo) (M++N).
      1,3: solveLL...
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      rewrite app_comm_cons.
      applyCutC H12 Hj.
      rewrite app_comm_cons.
      applyCutC H12 Hj.      
     ** 
      apply BipoleReasoning in H1...
      apply FocusingWith in H10...
      PosNegAll loc...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               solveSignature1.
               rewrite secCEncode.
      TFocus (BinBipole OR_BODY Left F1 G). 
      LLTensor [d| t_bin OR F1 G|] x0.
      simpl. LLRelease. LLWith.
      1-2: LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: solveSignature1.
      1-2 : rewrite secCEncode.
      applyCutC H10 Hj.
      applyCutC H12 Hj.
     
      checkPermutationCases H12.
      apply FocusingWith in H10...
      TFocus (BinBipole OR_BODY Left F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL...
      LLRelease.
      LLWith. 1-2: LLStore.
      rewrite app_comm_cons.
      applyCutC H13 Hj.
      rewrite app_comm_cons.
      applyCutC H14 Hj.
   * (* 3/6 - INIT *) 
   apply FocusingInitRuleU in H1...
             PosNegAll loc...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode loc M ++ (CEncode loc N ++ L)).      
                 
             apply  AbsorptionLSet'...
             apply setTCEncode...
             solveSignature1.
             rewrite secCEncode.
             TFocus (RINIT OO).
             LLTensor [u| OO |] [d| OO |].
             
                checkPermutationCases H9.
                
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
               
                checkPermutationCases H9.
           
                { clear H8.
                   simpl. 
                   PosNeg loc.
                   intro; intros...
                   simpl...
                   apply seqNtoSeq in Hj.
               refine (WeakTheory _ _ Hj)...
               apply TheoryEmb1. }
               
                
                apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H7.
                checkPermutationCases H9.
                rewrite H7.
                apply contraction with (F:=(x, d| FC |))...
                apply allU.
                rewrite <- H7.
                eapply PosFS with (a:=loc)...
                intro;intros...
               apply seqNtoSeq in Hj.
               refine (WeakTheory _ _ Hj)...
               apply TheoryEmb1.
               
               
               rewrite <- (app_nil_l N).
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
  
   * (* 4/6 - BOX *)  
      inversion H6...
      ** apply BipoleReasoning in H1...
                simpl in H11.
                apply FocusingBang in H10...
                PosNegAll loc...
               1-2: intro;intros...
                rewrite CEncodeApp...
                rewrite Permutation_app_comm.
                rewrite app_assoc.
                apply weakeningGen_rev...
                rewrite Permutation_app_comm;simpl.
                
                TFocus (UnBipole (BOX_BODY a) Right F1).
                LLTensor.
                simpl...   
                init2 loc L.
                solveSignature1.
               
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x2) (CK:=[]) (CN:=(loc, u| t_ucon (BOX_BODY a).(ucon) F1 |) ::x3)...
                solveSignature1.
                rewrite H10...
                simpl...
                LLStore.
                apply seqNtoSeq in H16.
                refine(WeakTheory _ _ H16).
                apply TheoryEmb1.
               
               checkPermutationCases H12.

      { (** BOX Right is principal *)
          clear H11.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
           3:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H14...
      simpl. solveLL.
      checkPermutationCases H15.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H5...
      inversion H13...
      solveF.
      inversion H13...
      solveF. }
      
      apply BipoleReasoning in H5...
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (M++x1).
      rewrite H14...
      simpl...       
                 checkPermutationCases H15.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
                    
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDRight.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
                apply FocusingWith in H13...
                TFocus (BinBipole AND_BODY Right F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteANDLeft.
                applyCutC Hi H12.
                applyCutC Hi H12.
                checkPermutationCases H15.
                 
                apply FocusingPlus in H13...
                all:TFocus (BinBipole AND_BODY Left F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORRight.
                applyCutC Hi H12.
                applyCutC Hi H12.
                 checkPermutationCases H15.
                apply FocusingPlus in H13...
                all:TFocus (BinBipole OR_BODY Right F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.           
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteORLeft.
                applyCutC Hi H13.
                applyCutC Hi H15.
                checkPermutationCases H15.
        
                apply FocusingWith in H13...
                TFocus (BinBipole OR_BODY Left F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll loc...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode loc N ++ (CEncode loc M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
              solveSignature1. 
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H11.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg loc.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H7.
                rewrite H12.
                TFocus (NEG (t_ucon BOX F1) loc).
                inversion H5...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=loc)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Modal Case *)   
            inversion H1...     
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingBang in H13...
                PosNegAll loc...
               1-2: intro;intros...
                rewrite CEncodeApp...
                rewrite app_assoc_reverse.
                apply weakeningGen...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x3) (CK:=[]) (CN:=(loc, u| t_ucon (BOX_BODY a).(ucon) F |) ::x4)...
                solveSignature1.
                rewrite H13...
                simpl...
                LLStore.
                apply seqNtoSeq in H19.
                refine(WeakTheory _ _ H19).
                apply TheoryEmb1.
               
               checkPermutationCases H15.
               
               apply FocusingBang in H13...
               apply WeakPosNegAll with (a:=loc)...
                1-2: intro;intros...
                
                TFocus (UnBipole (BOX_BODY a) Right F).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x5) (CK:=[]) (CN:=x6)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H21.
                refine(WeakTheory _ _ H21).
                apply TheoryEmb1.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor [d| t_ucon (BOX_BODY a).(ucon) F|] (M++x1).       rewrite H14...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H11.
                applyCutC Hi H11.
                apply allU.
                
                checkPermutationCases H15.
         { clear H14.
                    
           apply @PosNegSetT' with (a:=loc)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           eapply GeneralCut' with (C:=dual ((BOX_BODY a).(ru_leftBody) F1))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((BOX_BODY a).(ru_rightBody) F1))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN n1)).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H5 _)...
           apply weakeningAll...
                    
           apply BOX_CUTCOHERENT... 
           
           simpl.
           apply FocusingQuest in H13...
           apply FocusingBang in H10...
                simpl...
                apply weakeningGen... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x2) (CK:=[]) (CN:=x3)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H17.
                refine(WeakTheory _ _ H17).
                apply TheoryEmb1.
                
           simpl.
           apply FocusingQuest in H13...
           LLRelease. LLStoreC.
           rewrite <- Permutation_midle.
           apply AbsorptionLSet'...
           apply setTCEncode...
           solveSignature1.
           rewrite <- Permutation_midle.
           apply AbsorptionLSet'...
           apply setTCEncode...
           solveSignature1.
           rewrite !secCEncode.
           
                apply weakeningN with (F:=(a, d| F1 |)) in Hi...
                LLSwapC Hi.
                LLSwapC H8.
                applyCutC Hi H8.
                apply allU.         }                
      
                apply FocusingQuest in H13...
                TFocus (UnBipole (BOX_BODY a) Left F).
                LLTensor (@nil oo) (M++N). 
                solveLL...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F |)) in Hi...
                LLSwapC Hi.
                LLSwapC H15.
                applyCutC Hi H15.
                apply allU.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO loc).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            
            checkPermutationCases H14.
                 { clear H13. 
               apply FocusingQuest in H12...
               eapply contractionN in H8...
                applyCutC Hi H8.
               apply allU. 
      }
            apply FocusingQuest in H12...
           
            TFocus (POS OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            solveSignature1.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO loc).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(loc, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            solveSignature1.  }
               
               apply FocusingBang in H10...
               apply WeakPosNegAll with (a:=loc)...
                1-2: intro;intros...
                
                TFocus (UnBipole (BOX_BODY a) Right F1).
                LLTensor.
                simpl... solveLL.
                simpl... 
                createWorld.
                solveSignature1.
                eapply @GenK4RelUT' with (C4:=x4) (CK:=[]) (CN:=x5)...
                solveSignature1.
                simpl...
                LLStore.
                apply seqNtoSeq in H18.
                refine(WeakTheory _ _ H18).
                apply TheoryEmb1.
     ** apply BipoleReasoning in H1...
          simpl in H11.
                apply FocusingQuest in H10...
                TFocus (UnBipole (BOX_BODY a) Left F1).
                LLTensor [d| t_ucon (BOX_BODY a).(ucon) F1|] (x0++N).       
                rewrite H11...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F1 |)) in Hj...
                LLSwapC Hj.
                LLSwapC H8.
                applyCutC H8 Hj.
                apply allU.
                
                checkPermutationCases H12.
                apply FocusingQuest in H10...
                TFocus (UnBipole (BOX_BODY a) Left F1).
                LLTensor (@nil oo) (M++N). 
                solveLL...
                simpl. LLRelease. LLStoreC.
                apply weakeningN with (F:=(a, d| F1 |)) in Hj...
                LLSwapC Hj.
                LLSwapC H12.
                applyCutC H12 Hj.
                apply allU.
             
   * (* 5/6 - POS *)
      apply BipoleReasoning in H1...
      apply FocusingQuest in H9...
      rewrite H10.
      rewrite <- app_comm_cons.
      PosNeg loc.
      intro; intros...
      simpl.
      eapply weakeningN with (F:=(loc, d| OO |)) in Hj...
      LLSwapC H8.
      LLSwapC Hj.
      applyCutC H8 Hj.
      apply allU.
      
      checkPermutationCases H11.
      apply FocusingQuest in H9...
      rewrite H7.
      apply contraction with (F:=(x0, d| OO |))...
      apply allU.
      rewrite <- H7.
      apply PosFS with (a:=loc)...
      intro;intros...
      
      eapply weakeningN with (F:=(loc, d| OO |)) in Hj...
      LLSwapC H11.
      LLSwapC Hj.
      applyCutC H11 Hj.
      apply allU.
   * (* 6/6 - NEG *)
      apply BipoleReasoning in H1...
      apply FocusingQuest in H9...
      rewrite H10.
      rewrite <- app_comm_cons.
      PosNeg loc.
      intro; intros...
      simpl.
      eapply weakeningN with (F:=(loc, u| OO |)) in Hj...
      LLSwapC H8.
      LLSwapC Hj.
      applyCutC H8 Hj.
      apply allU.
      
      checkPermutationCases H11.
      { 
       apply FocusingQuest in H9...
        eapply contractionN in H9...
            applyCutC H9 Hj.
            apply allU. 
     }
      
      apply FocusingQuest in H9...
      rewrite H7.
      apply contraction with (F:=(x0, u| OO |))...
      apply allU.
      rewrite <- H7.
      apply NwgFS with (a:=loc)...
      intro;intros...
      
      eapply weakeningN with (F:=(loc, u| OO |)) in Hj...
      LLSwapC H11.
      LLSwapC Hj.
      applyCutC H11 Hj.
      apply allU.
  Qed.    
  
  
       Lemma KT4CutL F F0 FC L M N a h n0 n1 n' n:
     mt a = true -> m4 a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutC h a -> 
     seqN (KT4 a) (S n0) L (u| FC | :: M) (UP []) ->
     seqN (KT4 a) (S n1) L (d| FC | :: N) (UP []) ->
     KT4 a F ->
     ~ IsPositiveAtom F ->
     seqN (KT4 a) n0 L (u| FC | :: M) (DW F) ->
     KT4 a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (KT4 a) n1 L (d| FC | :: N) (DW F0) ->
     seq (KT4C a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros H4 H4' Heqh isFFC lngF HRel isFM isFN isFL. 
    intro CutHC.
    intros Hi Hj.
    intros H H0 H1 H2 H3 H5.

   eapply AbsorptionL with (i:=loc) in Hi...
   eapply AbsorptionL with (i:=loc) in Hj...
   eapply AbsorptionL with (i:=loc) in H1...
   eapply AbsorptionL with (i:=loc) in H5...
   
   eapply KT4CutC with
       (F:=F) (F0:=F0)
       (FC:=FC) (h:=h) (a:=a) (n':=n') (n0:=n0) (n1:=n1)...
    
    all: solveSignature1.   
   Qed.    
   
Theorem KT4CutStepC:
    forall n n' a i j FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true ->
    m4 a = true -> 
    n' <= n ->
   ( seqN  (KT4 a) i ((loc,u|FC|)::L) M  (UP []) -> 
    seqN  (KT4 a) j ((loc,d|FC|)::L) N  (UP []) ->
    seq   (KT4C a (pred n)) L (M++N)  (UP [])).
  Proof with CutTacPOSNEG;solveSignature1.
   intros.
   remember (plus i j) as h.
    
   revert dependent L.
   revert dependent M.
   revert dependent N.
   revert dependent FC.
   revert dependent i.
   revert dependent n.
   revert j n'.
    
   induction h using strongind;intros *.
   - intros... 
      -- intros;sauto.
         symmetry in Heqh.
         apply plus_is_O in Heqh.
         destruct Heqh;subst.
         inversion H7.
    - intros HRel i Heqh FC isFFC lngF N isFN M isFM L isFL.
       intros Hi Hj.
       
        assert(CutC h a).
        { unfold CutC;intros.
            revert H13.
            revert H12.
            eapply H with (m:=m) (n':=n'0)... }
       
        clear H.
        rename H0 into CutHC.
        
        inversion Hi...
        + apply RemoveNotPos1 in H0;sauto...
            intro HF.
            inversion HF;subst;inversion H...
        + apply InUNotPos in H2;sauto...
        + apply RemoveNotPos2 in H2;sauto...
        + inversion Hj...
            ++ apply RemoveNotPos1 in H3;sauto...
                   intro HF.
                   inversion HF;subst;inversion H2...
            ++ apply InUNotPos in H7;sauto...
            ++ apply RemoveNotPos2 in H7;sauto...
            ++
            
        eapply KT4CutC with
       (F:=F) (F0:=F0)
       (FC:=FC) (h:=h) (a:=a) (n':=n') (n0:=n0) (n1:=n1)...
  Qed. 
 
Theorem KT4CutStep:
    forall n n' a FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true -> 
    m4 a = true -> 
    n' <= n ->
   ( seq  (KT4 a) L (u|FC|::M)  (UP []) -> 
    seq  (KT4 a) L (d|FC|::N)  (UP []) ->
    seq   (KT4C a (pred n)) L (M++N)  (UP [])).
  Proof with CutTacPOSNEG.
   intros *.
   intros isFF lngF isFM isFN isFL Ha H4 Hn'. 
   intros Hi Hj.
   
   apply seqtoSeqN in Hi, Hj...
   eapply AbsorptionL with (i:=loc) in H0...
   eapply AbsorptionL with (i:=loc) in H...
   
   eapply KT4CutStepC  with
       (FC:=FC) (a:=a) (n':=n') (i:=x0) (j:=x)...
  all: solveSignature1.
  Qed.     
 
 Theorem KT4CutAdmissibility:
    forall n h a L M,
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true ->
    m4 a = true -> 
    seqN (KT4C a n) h L M (UP []) -> seq (KT4 a) L M (UP []) .
    Proof with CutTacPOSNEG.
    
    induction n;induction h using strongind ; intros *; 
    intros isFM isFL mtA Hf4 HC; try solve[inversion HC].
    *
    apply seqNtoSeq in HC.
    refine(WeakTheory _ _ HC).
    apply OOTheryCut0.
    *
    inversion HC;sauto;try solve [solveSignature1]. 
    apply RemoveNotPos1 in H2;sauto...
    intro HF.
    inversion HF;subst;inversion H1...
        
    apply InUNotPos in H4;sauto...
    apply RemoveNotPos2 in H4;sauto...
       
    inversion H1;sauto.
    + (* A formula from the theory was used *)
      (* Constants *)
      inversion H0...
      3:{ 
       apply BipoleReasoning in H3... 
       inversion H7... 
       solveF.
       inversion H7... 
       solveF. }
    3:{    
       apply BipoleReasoning in H3...
       Bipole FF Left.
       simpl in H8.
       LLTensor [d| t_cons FF |] x0.
       simpl...
       Bipole FF Left.
       simpl in H9.
       LLTensor (@nil oo) M.
       solveLL.
       simpl... }
   2:{
         apply BipoleReasoning in H3... 
       inversion H7... 
       solveF.
       inversion H7... 
       solveF.
  }    
       apply BipoleReasoning in H3...
       Bipole TT Right.
       simpl in H8.
       LLTensor [u| t_cons TT |] x0.
       simpl...
       Bipole TT Right.
       simpl in H9.
       LLTensor (@nil oo) M.
       solveLL.
       simpl...
     + (* A formula from the theory was used *)
      (* Connectives *)
      inversion H0...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingWith in H7...
       TFocus (BinBipole AND_BODY Right F0 G).
       LLTensor [u| t_bin AND F0 G |] x0.
       simpl. LLRelease. LLWith. 1-2: LLStore.
       eapply H in H7...
       eapply H in H9...
       simpl in H7.
       apply FocusingWith in H7...
       TFocus (BinBipole AND_BODY Right F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLRelease. LLWith. 1-2: LLStore.
       eapply H in H8...
       eapply H in H10...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingPlus in H7...
       TFocus (BinBipole AND_BODY Left F0 G).
       LLTensor [d| t_bin AND F0 G |] x0.
       simpl. LLPlusL. LLRelease. LLStore.
       eapply H in H6...
       TFocus (BinBipole AND_BODY Left F0 G).
       LLTensor [d| t_bin AND F0 G |] x0.
       simpl. LLPlusR. LLRelease. LLStore.
       eapply H in H6...
       
       simpl in H7.
       apply FocusingPlus in H7...
       TFocus (BinBipole AND_BODY Left F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLPlusL. LLRelease. LLStore.
       eapply H in H7...
       
       TFocus (BinBipole AND_BODY Left F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLPlusR. LLRelease. LLStore.
       eapply H in H7...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingPlus in H7...
       TFocus (BinBipole OR_BODY Right F0 G).
       LLTensor [u| t_bin OR F0 G |] x0.
       simpl. LLPlusL. LLRelease. LLStore.
       eapply H in H6...
       TFocus (BinBipole OR_BODY Right F0 G).
       LLTensor [u| t_bin OR F0 G |] x0.
       simpl. LLPlusR. LLRelease. LLStore.
       eapply H in H6...
       
       simpl in H7.
       apply FocusingPlus in H7...
       TFocus (BinBipole OR_BODY Right F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLPlusL. LLRelease. LLStore.
       eapply H in H7...
       
       TFocus (BinBipole OR_BODY Right F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLPlusR. LLRelease. LLStore.
       eapply H in H7...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingWith in H7...
       TFocus (BinBipole OR_BODY Left F0 G).
       LLTensor [d| t_bin OR F0 G |] x0.
       simpl. LLRelease. LLWith. 1-2: LLStore.
       eapply H in H7...
       eapply H in H9...
       simpl in H7.
       apply FocusingWith in H7...
       TFocus (BinBipole OR_BODY Left F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLRelease. LLWith. 1-2: LLStore.
       eapply H in H8...
       eapply H in H10...
    + (* A formula from the theory was used *)
      (* Init Rule *)
      apply FocusingInitRuleU in H3...
      ++ 
       TFocus (RINIT OO).
       LLTensor  [u| OO |] [d| OO |].
       ++ 
       TFocus (RINIT OO).
       LLTensor  [u| OO |] (@nil oo).
       solveLL.
       ++ 
       TFocus (RINIT OO).
       LLTensor (@nil oo)  [d| OO |].
       solveLL.
       ++ 
       TFocus (RINIT OO).
       LLTensor.
       init2 x0 x2.
       init2 x x1.
    + (* A formula from the theory was used *)
      (* Box *)
      inversion H0...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7. 
       apply FocusingBang' in H7...
       TFocus (UnBipole (BOX_BODY a) Right F0).
         
       LLTensor [u| t_ucon (BOX_BODY a).(ucon) F0 |] (@nil oo).
      simpl. createWorld. solveSignature1. eapply @GenK4RelUT' with (C4:=x2) (CK:=[]) (CN:=x3)...
                solveSignature1.
        simpl...
       LLStore.
       
       apply H in H13...
       srewrite H5 in isFL.
       rewrite map_app in isFL.
       apply Forall_app in isFL...
       
       simpl in H7. 
       apply FocusingBang' in H7...
       TFocus (UnBipole (BOX_BODY a) Right F0).
         
       LLTensor.
       solveLL...
    
      simpl. createWorld. solveSignature1. eapply @GenK4RelUT' with (C4:=x3) (CK:=[]) (CN:=x4)...
                solveSignature1.
        simpl...
       LLStore.
       
       apply H in H14...
       srewrite H7 in isFL.
       rewrite map_app in isFL.
       apply Forall_app in isFL...
      ++ 
       apply BipoleReasoning in H3...
       apply FocusingQuest in H7...
       TFocus (UnBipole (BOX_BODY a) Left F0).
         
       LLTensor [d| t_ucon (BOX_BODY a).(ucon) F0 |] x0.
       
      simpl. LLRelease. LLStoreC. 
       apply H in H5...

       apply FocusingQuest in H7...
       TFocus (UnBipole (BOX_BODY a) Left F0).
         
       LLTensor (@nil oo) M.
       solveLL...
      simpl. LLRelease. LLStoreC. 
       apply H in H7... 
    + (* A formula from the theory was used *)
      (* POS *)
       apply BipoleReasoning in H3...
       inversion H6...
       inversion H10...
       2: solveF.
       TFocus (POS OO loc). 
       LLTensor [d| OO|] x0.
       LLRelease. LLStoreC.
       eapply H in H11...
       
       inversion H6...
       inversion H11...
       2: solveF.
       TFocus (POS OO loc). 
       LLTensor (@nil oo) M.
       solveLL.
       LLRelease. LLStoreC.
       eapply H in H12...
    + (* A formula from the theory was used *)
      (* NEG *)
       apply BipoleReasoning in H3...
       inversion H6...
       inversion H10...
       2: solveF.
       TFocus (NEG OO loc). 
       LLTensor [u| OO|] x0.
       LLRelease. LLStoreC.
       eapply H in H11...
       
       inversion H6...
       inversion H11...
       2: solveF.
       TFocus (NEG OO loc). 
       LLTensor (@nil oo) M.
       solveLL.
       LLRelease. LLStoreC.
       eapply H in H12...
    + (* A formula from the theory was used *)
      (* Linear Cut *)
       inversion H0...
       apply FocusingTensor in H3...
       rewrite H9.
       apply H in H5...
       apply H in H11...
       2-3: OLSolve.
       
       assert(seq (KT4C a (pred ((S n)))) L (x1 ++ x0) (UP [])).
       refine (KT4CutStep _ H7 _ _ _ _ _ _ H11 H5)...
       simpl in H3.
       apply seqtoSeqN in H3...
       eapply IHn in H3...
       2-3: OLSolve.
       LLExact H3.
 Qed.
 
End KT4Cut.