Require Import MMLL.OL.CutCoherence.LNSi.LJInv.
         
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section LJCut.

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
     (seqN (LJ a) i ((loc,u|FC|)::L) M (UP []) ->
     seqN (LJ a) j ((a,d|FC|)::L) N (UP []) -> 
     seq (LJC a (pred n)) L (M ++ N) (UP [])).
 
Ltac CutTacPOSNEG := sauto;
  try
    match goal with
    | [ |- isFormula _] => constructor;auto
    | [ |- IsPositiveAtomFormula _] =>  constructor;auto
    | [ |- LJC _ _] => autounfold; solve[constructor;constructor;auto]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
      solve [apply PositiveAtomIn in H';auto;contradiction]
    | [ H: seqN _ _ _ _ (DW zero) |- _] => invTri H
    | [ H: seq  _ _ _ (DW zero) |- _] => invTri' H
    | [ |- LJC _ _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [ |- LJ _ ]=> autounfold;solve [repeat (constructor;auto)]
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

(* ; [do 2 constructor;OLSolve | solveBipole | ].
 *)
Tactic Notation "Bipole"  constr(B) constr(S) constr(F) constr(G):= 
     match B with
     | AND => TFocus (BinBipole AND_BODY S F G)
     | OR => TFocus (BinBipole OR_BODY S F G)
     | IMP => TFocus (BinBipole IMP_BODY S F G) 
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

 
Ltac applyCutC Hl Hr :=
 match goal with
  [ C: CutC _ _, 
    Hc: lengthUexp ?P ?n |- seq _ ?L (?M++?N) _  ] =>
    match type of Hl with
      | seqN _ ?l ((loc, u| ?P|)::?L) ?M _  =>
         match type of Hr with
         | seqN _ ?r ((?a, d| ?P|)::?L) ?N _ =>
           let H' := fresh "H" in assert(H' : l + r = l + r) by auto;
           refine(C _ _ _ _ _ _ _ _ _ _  H'  _ _ Hc _ _ _ _ _ Hl Hr);
           CutTacPOSNEG
          | _ => idtac "Debug " Hr
          end
     | _ => idtac "Debug " Hl
   end
end.   

 

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
   
               
 Ltac permuteIMPRight :=              
 match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.

          
  Context  {USI:UnbSignature}.
  Context  {UND:UnbNoDSignature}.

      
  Lemma LJCutC F F0 FC L M N a h n0 n1 n' n:
     mt a = true ->
    m4 a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutC h a ->
     seqN (LJ a) (S n0) ((loc,u| FC |) :: L) M (UP []) ->
     seqN (LJ a) (S n1) ((a,d| FC |) :: L) N (UP []) ->
     LJ a F ->
     ~ IsPositiveAtom F ->
     seqN (LJ a) n0 ((loc,u| FC |) :: L) M (DW F) ->
     LJ a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (LJ a) n1 ((a,d| FC |) :: L) N (DW F0) ->
     seq (LJC a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros H4 H4a Heqh isFFC lngF HRel isFM isFN isFL. 
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
            -- apply BipoleReasoning in H5...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                 simpl in H14.
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ ?N (UP []) ] => 
        
        apply FocusingBangPar in H1;sauto;
        TFocus (BinBipole (IMP_BODY a) Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (@nil oo)
   end.
    apply weakeningGen...
    apply weakeningGen...
     checkPermutationCases H13.
     2:{
      createWorld; solveSignature1.
     
      apply GenK4RelUT' with (C4:= x5) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H20.
               refine (WeakTheory _ _ H20)...
               apply TheoryEmb1. }
               
        LLrew1 H11 H20.       
        apply InversionTT with (n:=(pred n)) in H20...
        createWorld; solveSignature1.
     
      apply GenK4RelUT' with (C4:= x0) 
                        (CK:=[])
                        (CN:=x6);solveSignature1...
        rewrite H11 in H16. solveSE.                
        rewrite H11 in H17. solveSE.                
        rewrite H11 in H18. solveLT.                
        
         simpl... 
         symmetry in H13.
             srewrite H13 in isFL.
             rewrite map_app in isFL. OLSolve. 
      
        simpl in H15.
       checkPermutationCases H15.
  
      rewrite Permutation_app_comm.
                specialize (posDestruct' isFM) as HC...
                rewrite H5.
                rewrite app_assoc.
                apply NegSetP with (a:=loc)...
                 rewrite H5 in isFM...
                apply PositiveAtomREOLFormula.
                OLSolve.
                apply PosSetP with (a:=a)...
                 rewrite H5 in isFM...
                apply PositiveAtomLEOLFormula.
                OLSolve.
            
   apply weakeningGen...
     apply weakeningGen...
               apply FocusingBangPar in H13...
        TFocus (BinBipole (IMP_BODY a) Right F G); 
        simpl;
        LLTensor;[solveLL;sauto|].
         createWorld; solveSignature1.
      checkPermutationCases H16.
     2:{ 
      apply GenK4RelUT' with (C4:= x7) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H22.
               refine (WeakTheory _ _ H22)...
               apply TheoryEmb1. }
        LLrew1 H15 H22.       
        apply InversionTT with (n:=(pred n)) in H22...
      
      apply GenK4RelUT' with (C4:= x0) 
                        (CK:=[])
                        (CN:=x8);solveSignature1...
        rewrite H15 in H18. solveSE.                
        rewrite H15 in H19. solveSE.                
        rewrite H15 in H20. solveLT.                
        
         simpl... 
         symmetry in H16.
             srewrite H16 in isFL.
             rewrite map_app in isFL. OLSolve. 
            -- apply BipoleReasoning in H5...
            assert(isX1: IsPositiveAtomFormulaL x1) by OLSolve.
                apply FocusingTensor in H13...
                simpl in H13.
                 specialize (posDestruct' isFM) as HC...
                 refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                
                TFocus (BinBipole (IMP_BODY a) Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite app_assoc_reverse.
                1-2: rewrite <- H5.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                
                TFocus (BinBipole (IMP_BODY a) Left F G). 
                simpl.
                LLTensor (@nil oo) N.
                rewrite app_assoc.
                apply weakeningGen... 
                solveLL...
                LLTensor x5 x6. 
                
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite app_assoc_reverse.
                1-2: rewrite <- H5.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                
                checkPermutationCases H12.
                clear H11.
                rewrite Permutation_app_comm...
                simpl.
                apply NegF with (a:=loc)...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                rewrite app_assoc.
                apply weakeningGen...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                rewrite app_assoc.
                apply weakeningGen...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
apply contraction with (F:=(x1, u| t_cons TT_BODY.(cte) |))...         solveSignature1.
                rewrite <- H12.
                eapply NwgFS with (a:=loc)...
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               simpl...
               
               specialize (posDestruct' isFM) as HC...
               rewrite <- (app_nil_r M).
               refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                rewrite app_assoc.
                apply weakeningGen...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
              apply contractionN in H7...
            applyCutC Hi H7.
            solveSignature1.           
            
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.
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
            apply allU.
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
            apply allU.  }
   
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
      TFocus (BinBipole AND_BODY Right F1 G). 
      LLTensor [u| t_bin AND F1 G|] (x0++N).
      rewrite H11...
      simpl. LLRelease. LLWith.
      1-2: LLStore.
      rewrite app_comm_cons.
      applyCutC H10 Hj.
      rewrite app_comm_cons.
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
               specialize (posDestruct' isFM) as HC...
               specialize (posDestruct' isFN) as HC...
                refine (LinearToClassicAll _ _ _ _ _ _ _ _ _ H4 H5 _)...
                
                rewrite <- (app_nil_r []).
           
           Import SL.CutElimination.
           
           eapply GeneralCut' with (C:=dual ((AND_BODY.(rb_leftBody) F1 G)))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((AND_BODY.(rb_rightBody) F1 G)))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H7 _)...
           apply weakeningAll...
                    
           apply AND_CUTCOHERENT... 

           simpl.
           apply FocusingWith in H10...
           LLRelease. 
           LLWith. 
           1-2: LLStore.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite app_comm_cons. 
           LLPerm ((u| F1 | :: M) ++ N).
           rewrite !REncodeApp.
           rewrite !LEncodeApp.
           rewrite H4, H5...
           applyCutC H14 Hj.
           LLPerm ((u| G | :: M) ++ N).
           rewrite !REncodeApp.
           rewrite !LEncodeApp.
           rewrite H4, H5...
           applyCutC H15 Hj. 
           
           simpl.
           apply FocusingWith in H10...
           apply FocusingPlus in H13...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.  
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle.
           LLPerm (M++(d| F1 | :: N) ).
           rewrite !REncodeApp.
           rewrite !LEncodeApp.
           rewrite H4, H5...
           applyCutC Hi H11.
           LLPerm (M++(d| G | :: N) ).
           rewrite !REncodeApp.
           rewrite !LEncodeApp.
           rewrite H4, H5...
           applyCutC Hi H11.
           }

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
            -- apply BipoleReasoning in H5...
               {
                simpl in H14.
                apply FocusingBangPar in H13...
                checkPermutationCases H11.
                
                2:{
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2  _ _ _ _ _ _ H5 _)...
                
                TFocus (BinBipole (IMP_BODY a) Right F G0). 
                simpl;
                LLTensor [u| t_bin IMP F G0 |] (@nil oo).
                apply weakeningGen;solveSignature1...
                apply weakeningGen;solveSignature1...
                createWorld;solveSignature1.
                apply GenK4RelUT' with (C4:= x3) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H19.
               refine (WeakTheory _ _ H19)...
               apply TheoryEmb1. }
               
      rewrite Permutation_app_comm.
      simpl...
      apply NegF with (a:=loc)...        
      specialize (posDestruct' isFM) as HC...
      rewrite <- (app_nil_r M).
      refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
      inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H13.
      LLTensor;LLRelease;LLStore.
      1:{
      apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H13.
      LLTensor  [d| F1 |] M ;LLRelease;LLStore.
      1:{
      apply PosF with (a:=a)...  
      apply PosF with (a:=a)...  
      simpl...
      LLPerm((loc, u| t_bin IMP F G0 |) ::(a, d| F1 |)
   :: (a, d| G |) ::  L).
   apply AbsorptionL'...
   
      eapply InversionANDL with (m:=(S (S (S (S (S (S (S x2)))) + length x3))))... }
      
   apply AbsorptionL'...
   
      LLPerm (u| G | :: M++[u| t_bin IMP F G0 | ]).
      apply FocusingWith in H10...
      assert(Hh: x6 + S (S (S (S (S (S (S x2)))) + length x3)) = x6 + S (S (S (S (S (S (S x2)))) + length x3))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H20 Hj); CutTacPOSNEG. }
        
      apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      apply NegF with (a:=loc)...  
      eapply InversionANDR1 with (Q:=G) (m:=(S (S x)))...
      LLSwap.
      apply weakeningN;solveSignature1... }
      
       apply FocusingBangPar in H13...
       checkPermutationCases H15.
       specialize (posDestruct' isFM) as HC...
       rewrite <- (app_nil_r M).
       refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
        checkPermutationCases H13.
     2:{
        apply weakeningGen;solveSignature1...
        apply weakeningGen;solveSignature1...
        TFocus (BinBipole (IMP_BODY a) Right F G0); 
        simpl;
        LLTensor. 
        solveLL.
           createWorld; solveSignature1.
   
      apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x8);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H20.
               refine (WeakTheory _ _ H20)...
               apply TheoryEmb1. }
               
          inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H13.
      LLTensor;LLRelease;LLStore.
      1:{
      apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H13.
      LLTensor  [d| F1 |] M ;LLRelease;LLStore.
      1:{
      apply PosF with (a:=a)...  
      apply PosF with (a:=a)...  
      simpl...
      eapply InversionANDL with (m:=(S (S (S (S (S (S (S x3)))) + length x4))))... }
         
      apply FocusingWith in H10...
      LLPerm (u| G | :: M++[]).
      assert(Hh: x9 + S (S (S (S (S (S (S x3)))) + length x4)) = x9 + S (S (S (S (S (S (S x3)))) + length x4))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H23 Hj); CutTacPOSNEG. }
        
      apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      apply NegF with (a:=loc)...  
      simpl...
      eapply InversionANDR1 with (Q:=G) (m:=(S (S x)))...
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen;solveSignature1...
                apply weakeningGen;solveSignature1... 
                solveLL.
                LLTensor x5 x6.
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             TFocus (RINIT OO).
             LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                rewrite Permutation_app_comm...
                simpl.
                apply NegF with (a:=loc)...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                checkPermutationCases H12.
                specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
                TFocus (NEG (t_bin AND F1 G) loc).
                inversion H4. 
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
                 specialize (posDestruct' isFM) as HC...
               rewrite <- (app_nil_r M).
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.
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
            apply allU.
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
            apply allU.  }
            
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
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole AND_BODY Left F1 G). 
      1-2: LLTensor [d| t_bin AND F1 G|] (x0++N).
      1,3: rewrite H11...
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2: rewrite app_comm_cons.
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
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole OR_BODY Right F1 G).
      1-2: LLTensor [u| t_bin OR F1 G|] (x0++N).
      1,3: rewrite H11... 
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2 : rewrite app_comm_cons.
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
          specialize (posDestruct' isFM) as HC...
               specialize (posDestruct' isFN) as HC...
                refine (LinearToClassicAll _ _ _ _ _ _ _ _ _ H4 H5 _)...
                
                rewrite <- (app_nil_r []).
          
           eapply GeneralCut' with (C:=dual ((OR_BODY.(rb_leftBody) F1 G)))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((OR_BODY.(rb_rightBody) F1 G)))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H7 _)...
           apply weakeningAll...
                    
           apply OR_CUTCOHERENT... 

           simpl.
           apply FocusingWith in H13...
           apply FocusingPlus in H10...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1: LLPerm (u| F1 | :: M ++ N).
           3: LLPerm (u| G | :: M ++ N).
           1,3: rewrite REncodeApp, LEncodeApp, H4, H5...
           1,2: rewrite app_comm_cons.
           1,2: applyCutC H11 Hj.
           
           simpl.
           apply FocusingWith in H13...
           LLRelease; LLWith; LLStore. 
           1,2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1,2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1,2: rewrite !secCEncode.
           1: LLPerm (M ++ d| F1 | :: N).
           3: LLPerm (M ++ d| G | :: N).
           1,3: rewrite REncodeApp, LEncodeApp, H4, H5...
           applyCutC Hi H14.
           applyCutC Hi H15. }
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
            -- apply BipoleReasoning in H5...
          {
                simpl in H14.
                apply FocusingBangPar in H13...
                checkPermutationCases H11.
                
                2:{
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                
                TFocus (BinBipole (IMP_BODY a) Right F G0). 
                simpl;
                LLTensor [u| t_bin IMP F G0 |] (@nil oo).
                apply weakeningGen;solveSignature1...
                apply weakeningGen;solveSignature1...
                createWorld;solveSignature1.
                apply GenK4RelUT' with (C4:= x3) 
                        (CK:=[])
                        (CN:=x0);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H19.
               refine (WeakTheory _ _ H19)...
               apply TheoryEmb1. }
               
      rewrite Permutation_app_comm.
      simpl...
      apply NegF with (a:=loc)...        
      specialize (posDestruct' isFM) as HC...
      rewrite <- (app_nil_r M).
      refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
      inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H13.
      LLTensor;LLRelease;LLStore.
      apply weakeningGen;solveSignature1... 
      apply weakeningGen;solveSignature1... 
      apply PosF with (a:=a)...  
      simpl...
   
      eapply InversionORL1 with (Q:=G) (m:=(S (S (S (S (S (S (S x2)))) + length x3))))...
      LLSwap.
      apply AbsorptionL...
   
     apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H13.
      LLTensor (@nil oo) (u| F1 |::M)   ;LLRelease;LLStore.
      apply PosF with (a:=a)...  
      simpl...
    
      eapply InversionORL2 with (P:=F1) (m:=(S (S (S (S (S (S (S x2)))) + length x3))))...
      LLSwap.
      apply AbsorptionL...
      
      apply FocusingPlus in H10...
      apply NegF with (a:=loc)...  
      simpl...
      apply weakening;solveSignature1...
      apply AbsorptionL'...
      
      LLPerm (u| F1| :: M++[u| t_bin IMP F G0 | ]).
      assert(Hh: x6 + S (S (S (S (S (S (S x2)))) + length x3)) = x6 + S (S (S (S (S (S (S x2)))) + length x3))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H14 Hj); CutTacPOSNEG. 
        LLSwap.
      apply NegF with (a:=loc)...  
      simpl...
      apply weakening;solveSignature1...
      apply AbsorptionL'...
      
      LLPerm (u| G| :: M++[u| t_bin IMP F G0 | ]).
      assert(Hh: x6 + S (S (S (S (S (S (S x2)))) + length x3)) = x6 + S (S (S (S (S (S (S x2)))) + length x3))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H14 Hj); CutTacPOSNEG. 
   }
      
       apply FocusingBangPar in H13...
       checkPermutationCases H15.
       specialize (posDestruct' isFM) as HC...
       rewrite <- (app_nil_r M).
       refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
        checkPermutationCases H13.
     2:{
        apply weakeningGen;solveSignature1...
        apply weakeningGen;solveSignature1...
        TFocus (BinBipole (IMP_BODY a) Right F G0); 
        simpl;
        LLTensor. 
        solveLL.
           createWorld; solveSignature1.
   
      apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x8);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H20.
               refine (WeakTheory _ _ H20)...
               apply TheoryEmb1. }
               
          inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H13.
      LLTensor;LLRelease;LLStore.
      apply weakeningGen;solveSignature1... 
      apply weakeningGen;solveSignature1... 
      apply PosF with (a:=a)...  
      simpl...
  
      eapply InversionORL1 with (Q:=G) (m:=(S (S (S (S (S (S (S x3)))) + length x4))))...
      
     apply AbsorptionLSet'.
      apply setTCEncode...
      apply AbsorptionLSet'.
      apply setTCEncode...
      simpl...
      rewrite !secCEncode.
      rewrite <- H5.
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H13.
      LLTensor (@nil oo) (u| F1 |::M)   ;LLRelease;LLStore.
      apply PosF with (a:=a)...  
      simpl...
      eapply InversionORL2 with (P:=F1) (m:=(S (S (S (S (S (S (S x3)))) + length x4))))...
      
      apply FocusingPlus in H10...
      apply NegF with (a:=loc)...  
      simpl...
      apply weakening;solveSignature1...
      
      LLPerm (u| F1| :: M++[ ]).
      assert(Hh: x9 + S (S (S (S (S (S (S x3)))) + length x4)) = x9 + S (S (S (S (S (S (S x3)))) + length x4))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H21 Hj); CutTacPOSNEG. 
        LLSwap.
      apply NegF with (a:=loc)...  
      simpl...
      apply weakening;solveSignature1...
      
      LLPerm (u| G| :: M++[ ]).
      assert(Hh: x9 + S (S (S (S (S (S (S x3)))) + length x4)) = x9 + S (S (S (S (S (S (S x3)))) + length x4))) by auto.
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H21 Hj); CutTacPOSNEG.
        
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen;solveSignature1...
                apply weakeningGen;solveSignature1... 
                solveLL.
                LLTensor x5 x6.
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             TFocus (RINIT OO).
             LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                rewrite Permutation_app_comm...
                simpl.
                apply NegF with (a:=loc)...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                checkPermutationCases H12.
                specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H8.
                rewrite H12.
                TFocus (NEG (t_bin OR F1 G) loc).
                inversion H4. 
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
                 specialize (posDestruct' isFM) as HC...
               rewrite <- (app_nil_r M).
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.
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
            apply allU.
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
            apply allU.  }
            
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
      TFocus (BinBipole OR_BODY Left F1 G). 
      LLTensor [d| t_bin OR F1 G|] (x0++N).
      rewrite H11...
      simpl. LLRelease. LLWith;LLStore.
      1-2: rewrite app_comm_cons.
      applyCutC H10 Hj.
      applyCutC H12 Hj.
     
      checkPermutationCases H12.
      apply FocusingWith in H10...
      TFocus (BinBipole OR_BODY Left F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL...
      LLRelease.
      LLWith; LLStore.
      1,2: rewrite app_comm_cons.
      applyCutC H13 Hj.
      applyCutC H14 Hj.
      ** (* 5/6 - IMP Right *)
      apply BipoleReasoning in H1...
      specialize (posDestruct' isFN) as HC...
      rewrite Permutation_app_comm.
      refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
      apply FocusingBangPar in H10...
      TFocus (BinBipole (IMP_BODY a) Right F1 G); 
      simpl.
      LLTensor [u| t_bin IMP F1 G |] (@nil oo).
      checkPermutationCases H10.
     2:{
      apply weakeningGen...
     apply weakeningGen...
      createWorld; solveSignature1.
     
      apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H17.
               refine (WeakTheory _ _ H17)...
               apply TheoryEmb1. }
     
       
       rewrite H8 in H13. 
       inversion H13...
       solveSignature1.
   
       simpl in H12.
       checkPermutationCases H12.
      
     2:{
         apply FocusingBangPar in H10...
         specialize (posDestruct' isFN) as HC...
      rewrite <- (app_nil_r N).
      refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
      apply weakeningGen...
      apply weakeningGen...
        TFocus (BinBipole (IMP_BODY a) Right F1 G); 
        simpl.
 
        LLTensor.
        init2 x0 x2.
        checkPermutationCases H12.
        
        rewrite H12 in H14.
        inversion H14...
        solveSignature1.
      
      createWorld; solveSignature1.
     
      apply GenK4RelUT' with (C4:= x4) 
                        (CK:=[])
                        (CN:=x7);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H18.
               refine (WeakTheory _ _ H18)...
               apply TheoryEmb1. }
     
        { (** IMP Right is principal *)
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
            -- apply BipoleReasoning in H5...
                simpl in H14.
                apply FocusingBangPar in H10...
                apply FocusingBangPar in H13...
                checkPermutationCases H10.
                rewrite H7 in H15.
                inversion H15...
                solveSignature1.
                checkPermutationCases H11.
                2:{
                 
                TFocus (BinBipole (IMP_BODY a) Right F G0). 
                LLTensor [u| t_bin IMP F G0 |] (@nil oo). 
                createWorld; solveSignature1.
               apply GenK4RelUT' with (C4:= x5) 
                        (CK:=[])
                        (CN:=x1);solveSignature1...
                simpl... LLPar. do 2 LLStore.
                apply seqNtoSeq in H23.
               refine (WeakTheory _ _ H23)...
               apply TheoryEmb1. }
      { 
      apply NegF with (a:=loc)...
       inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      
      apply PosF with (a:=a)...  
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      2:{
      apply NegF with (a:=loc)...  
      simpl...
      LLPerm ((loc, u| t_bin IMP F G0 |) :: (loc, u| G |)
   :: (a, d| F1 |) :: L).
      apply weakening;solveSignature1.
      LLSwap.
      eapply InversionIMPR with (m:=(S (S (S (S (S (S (S x2)))) + length x3))))... }
     apply PosF with (a:=a)...  
      simpl...
       apply weakening;solveSignature1.
      apply weakening;solveSignature1.
     
       TFocus (BinBipole (IMP_BODY a) Right F G0). 
     LLTensor.
     
      simpl... solveLL.
      simpl...
       apply weakening;solveSignature1.
      rewrite <- H13 in H10.
      assert(SetK4 x1).
      rewrite H11 in H18.
      solveSE.
      assert(SetT x1).
      rewrite H11 in H20.
      solveSE.
      assert(LtX a x1).
      rewrite H11 in H21.
      solveLT.
      apply destructClassicSetK4 in H10...
      assert(SetK4 x9). 
      rewrite H28 in H5. 
      apply Forall_app in H5...
      assert(SetT x9). 
      rewrite H28 in H14. 
      apply Forall_app in H14...
      assert(LtX a x9). 
      rewrite H28 in H22. 
      apply Forall_app in H22...
      rewrite <- H13.
      rewrite H28, H30. 
      
      createWorld; solveSignature1.
               
      apply GenK4RelUT' with (C4:=x3++x9) 
                        (CK:=[])
                        (CN:=x10);solveSignature1...
         
        1-3: apply Forall_app... 
        rewrite H24...
        simpl...
        LLPar. do 2 LLStore.
        assert(seqN (LJ a) (S (S (S (S (S (S (S x2)))) + length x3)))
       ((loc, u| t_bin IMP F1 G |) :: (x3++x9)) [] 
       (UP [])).
         TFocus (BinBipole (IMP_BODY a) Right F1 G). 
     LLTensor.  simpl... solveLL.
     apply weakeningN;solveSignature1... 
     rewrite !Nat.add_succ_l.
      createWorld; solveSignature1.
               
      apply GenK4RelU with (C4:=x3) 
                        (CK:=[])
                        (CN:=x9);solveSignature1...
       
       rewrite <- !Nat.add_succ_l.               
        rewrite Nat.add_sub.          
       simpl...       
       rewrite PlusT_fixpoint'...
      assert(Hh: (S (S (S (S (S (S (S x2)))) + length x3))) + x=  (S (S (S (S (S (S (S x2)))) + length x3))) + x) by auto.
       LLPerm([]++[u| G0 |; d| F |] ).
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H32 _); CutTacPOSNEG. 
        symmetry in H13.
        srewrite H13 in isFL.
        rewrite map_app in isFL...
        apply Forall_app in isFL...
        srewrite H28 in H33.
        srewrite H30 in H34.
        rewrite map_app in H33, H34 ...
        apply Forall_app in  H33, H34...
        
        rewrite secondApp.
        apply Forall_app...
        srewrite H24.
        rewrite map_app...
        apply Forall_app...
        
        LLPerm (x8++(a, d| t_bin IMP F1 G |) :: (x7 ++ x9)).
        rewrite H24...
        apply weakeningGenN...
        LLExact H23.
        rewrite H11, H28...
        
       apply NegF with (a:=loc)...  
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      apply weakening;solveSignature1.
      apply PosF with (a:=a)...  
      simpl...
      LLSwap.
      apply AbsorptionL'...
      eapply InversionIMPL with (P:=F1) (m:=S (S (S (S (S (S (S x)))) + length x5)))... 
      
     apply NegF with (a:=loc)...  
      simpl...
       apply weakening;solveSignature1.
      apply weakening;solveSignature1.
     
       TFocus (BinBipole (IMP_BODY a) Right F G0). 
     LLTensor.
     
      simpl... solveLL.
      simpl...
       apply weakening;solveSignature1.
      rewrite <- H13 in H10.
      assert(SetK4 x1).
      rewrite H11 in H18.
      solveSE.
      assert(SetT x1).
      rewrite H11 in H20.
      solveSE.
      assert(LtX a x1).
      rewrite H11 in H21.
      solveLT.
      apply destructClassicSetK4 in H10...
      assert(SetK4 x9). 
      rewrite H28 in H5. 
      apply Forall_app in H5...
      assert(SetT x9). 
      rewrite H28 in H14. 
      apply Forall_app in H14...
      assert(LtX a x9). 
      rewrite H28 in H22. 
      apply Forall_app in H22...
      rewrite <- H13.
      rewrite H28, H30. 
      
      createWorld; solveSignature1.
               
      apply GenK4RelUT' with (C4:=x3++x9) 
                        (CK:=[])
                        (CN:=x10);solveSignature1...
         
        1-3: apply Forall_app... 
        rewrite H24...
        simpl...
        LLPar. do 2 LLStore.
        assert(seqN (LJ a) (S (S (S (S (S (S (S x2)))) + length x3)))
       ((loc, u| t_bin IMP F1 G |) :: (x3++x9)) [] 
       (UP [])).
         TFocus (BinBipole (IMP_BODY a) Right F1 G). 
     LLTensor.  simpl... solveLL.
     apply weakeningN;solveSignature1... 
     rewrite !Nat.add_succ_l.
      createWorld; solveSignature1.
               
      apply GenK4RelU with (C4:=x3) 
                        (CK:=[])
                        (CN:=x9);solveSignature1...
       
       rewrite <- !Nat.add_succ_l.               
        rewrite Nat.add_sub.          
       simpl...       
       rewrite PlusT_fixpoint'...
      assert(Hh: (S (S (S (S (S (S (S x2)))) + length x3))) + x=  (S (S (S (S (S (S (S x2)))) + length x3))) + x) by auto.
       LLPerm([]++[u| G0 |; d| F |] ).
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H32 _); CutTacPOSNEG. 
        symmetry in H13.
        srewrite H13 in isFL.
        rewrite map_app in isFL...
        apply Forall_app in isFL...
        srewrite H28 in H33.
        srewrite H30 in H34.
        rewrite map_app in H33, H34 ...
        apply Forall_app in  H33, H34...
        
        rewrite secondApp.
        apply Forall_app...
        srewrite H24.
        rewrite map_app...
        apply Forall_app...
        
        LLPerm (x8++(a, d| t_bin IMP F1 G |) :: (x7 ++ x9)).
        rewrite H24...
        apply weakeningGenN...
        LLExact H23.
        rewrite H11, H28... }
        
        checkPermutationCases H15.
        apply FocusingBangPar in H10...
        apply FocusingBangPar in H13...
              checkPermutationCases H15.
                rewrite H10 in H17.
                inversion H17...
                solveSignature1.
                checkPermutationCases H13.
                2:{     
                   TFocus (BinBipole (IMP_BODY a) Right F G0). 
                LLTensor.
                simpl... solveLL. 
                simpl...
                createWorld; solveSignature1.
               apply GenK4RelUT' with (C4:= x7) 
                        (CK:=[])
                        (CN:=x9);solveSignature1...
                simpl... LLPar. do 2 LLStore.
                apply seqNtoSeq in H25.
               refine (WeakTheory _ _ H25)...
               apply TheoryEmb1. }
     
       inversion lngF...
      TFocus(CUTL F1).
      apply oothc_cutln.
      apply ltn with (m:=n1)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      
      apply PosF with (a:=a)...  
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      2:{
      apply NegF with (a:=loc)...  
      simpl...
      LLSwap.
      eapply InversionIMPR with (m:=(S (S (S (S (S (S (S x4)))) + length x5))))... }
     apply PosF with (a:=a)...  
      simpl...
      apply weakening;solveSignature1.
      apply weakening;solveSignature1.
       TFocus (BinBipole (IMP_BODY a) Right F G0). 
     LLTensor.
      simpl... solveLL.
      simpl...
      rewrite <- H16 in H15.
      assert(SetK4 x9).
      rewrite H13 in H20.
      solveSE.
      assert(SetT x9).
      rewrite H13 in H22.
      solveSE.
      assert(LtX a x9).
      rewrite H13 in H23.
      solveLT.
      apply destructClassicSetK4 in H15...
      assert(SetK4 x12). 
      rewrite H31 in H5. 
      apply Forall_app in H5...
      assert(SetT x12). 
      rewrite H31 in H24. 
      apply Forall_app in H24...
      assert(LtX a x12). 
      rewrite H31 in H26. 
      apply Forall_app in H26...
      rewrite <- H16.
      rewrite H31, H33. 
      
      createWorld; solveSignature1.
               
      apply GenK4RelUT' with (C4:=x5++x12) 
                        (CK:=[])
                        (CN:=x13);solveSignature1...
         
        1-3: apply Forall_app... 
        rewrite H27...
        simpl...
        LLPar. do 2 LLStore.
        assert(seqN (LJ a) (S (S (S (S (S (S (S x4)))) + length x5)))
       ((loc, u| t_bin IMP F1 G |) :: (x5++x12)) [] 
       (UP [])).
         TFocus (BinBipole (IMP_BODY a) Right F1 G). 
     LLTensor.  simpl... solveLL.
     apply weakeningN;solveSignature1... 
     rewrite !Nat.add_succ_l.
      createWorld; solveSignature1.
               
      apply GenK4RelU with (C4:=x5) 
                        (CK:=[])
                        (CN:=x12);solveSignature1...
       
       rewrite <- !Nat.add_succ_l.               
        rewrite Nat.add_sub.          
       simpl...       
       rewrite PlusT_fixpoint'...
      assert(Hh: (S (S (S (S (S (S (S x4)))) + length x5))) + x=  (S (S (S (S (S (S (S x4)))) + length x5))) + x) by auto.
       LLPerm([]++[u| G0 |; d| F |] ).
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H35 _); CutTacPOSNEG. 
        symmetry in H16.
        srewrite H16 in isFL.
        rewrite map_app in isFL...
        apply Forall_app in isFL...
        srewrite H31 in H36.
        srewrite H33 in H37.
        rewrite map_app in H36, H37 ...
        apply Forall_app in  H36, H37...
        
        rewrite secondApp.
        apply Forall_app...
        srewrite H27.
        rewrite map_app...
        apply Forall_app...
        
        LLPerm (x11++(a, d| t_bin IMP F1 G |) :: (x10 ++ x12)).
        rewrite H27...
        apply weakeningGenN...
        LLExact H25.
        rewrite H13, H31...
        
       apply NegF with (a:=loc)...  
      TFocus(CUTL G).
      apply oothc_cutln.
      apply ltn with (m:=n2)...
      inversion H5.
      LLTensor;LLRelease;LLStore.
      apply weakening;solveSignature1.
      apply PosF with (a:=a)...  
      simpl...
      eapply InversionIMPL with (P:=F1) (m:=S (S (S (S (S (S (S x)))) + length x7)))... 
      
     apply NegF with (a:=loc)...  
      simpl...
       apply weakening;solveSignature1.
      apply weakening;solveSignature1.
     
       TFocus (BinBipole (IMP_BODY a) Right F G0). 
     LLTensor.
     
      simpl... solveLL.
      simpl...
     rewrite <- H16 in H15.
      assert(SetK4 x9).
      rewrite H13 in H20.
      solveSE.
      assert(SetT x9).
      rewrite H13 in H22.
      solveSE.
      assert(LtX a x9).
      rewrite H13 in H23.
      solveLT.
      apply destructClassicSetK4 in H15...
      assert(SetK4 x12). 
      rewrite H31 in H5. 
      apply Forall_app in H5...
      assert(SetT x12). 
      rewrite H31 in H24. 
      apply Forall_app in H24...
      assert(LtX a x12). 
      rewrite H31 in H26. 
      apply Forall_app in H26...
      rewrite <- H16.
      rewrite H31, H33. 
      
      createWorld; solveSignature1.
            apply GenK4RelUT' with (C4:=x5++x12) 
                        (CK:=[])
                        (CN:=x13);solveSignature1...
         
        1-3: apply Forall_app... 
        rewrite H27...
        simpl...
        LLPar. do 2 LLStore.
        assert(seqN (LJ a) (S (S (S (S (S (S (S x4)))) + length x5)))
       ((loc, u| t_bin IMP F1 G |) :: (x5++x12)) [] 
       (UP [])).
         TFocus (BinBipole (IMP_BODY a) Right F1 G). 
     LLTensor.  simpl... solveLL.
     apply weakeningN;solveSignature1... 
     rewrite !Nat.add_succ_l.
      createWorld; solveSignature1.
               
      apply GenK4RelU with (C4:=x5) 
                        (CK:=[])
                        (CN:=x12);solveSignature1...
       
       rewrite <- !Nat.add_succ_l.               
        rewrite Nat.add_sub.          
       simpl...       
       rewrite PlusT_fixpoint'...
      assert(Hh: (S (S (S (S (S (S (S x4)))) + length x5))) + x=  (S (S (S (S (S (S (S x4)))) + length x5))) + x) by auto.
       LLPerm([]++[u| G0 |; d| F |] ).
       
        refine(CutHC _ _ _ _ _ _ _ _ _ _  Hh  _ _  lngF  _ _ _ _ _ H35 _); CutTacPOSNEG. 
        symmetry in H16.
        srewrite H16 in isFL.
        rewrite map_app in isFL...
        apply Forall_app in isFL...
        srewrite H31 in H36.
        srewrite H33 in H37.
        rewrite map_app in H36, H37 ...
        apply Forall_app in  H36, H37...
        
        rewrite secondApp.
        apply Forall_app...
        srewrite H27.
        rewrite map_app...
        apply Forall_app...
        
        LLPerm (x11++(a, d| t_bin IMP F1 G |) :: (x10 ++ x12)).
        rewrite H27...
        apply weakeningGenN...
        LLExact H25.
        rewrite H13, H31... 
           -- apply BipoleReasoning in H5...
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                { clear H14.
          specialize (posDestruct' isFM) as HC...
               specialize (posDestruct' isFN) as HC...
                refine (LinearToClassicAll _ _ _ _ _ _ _ _ _ H4 H5 _)...
                
                rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((IMP_BODY a).(rb_leftBody) F1 G))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((IMP_BODY a).(rb_rightBody) F1 G))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H9 _)...
           apply weakeningAll...
                    
           apply IMP_CUTCOHERENT... 
           
           simpl.
           apply FocusingBangPar in H10...
           checkPermutationCases H11.
           rewrite H11 in H15.
           inversion H15... solveSignature1.
           simpl...
           apply weakeningGen...
           apply weakeningGen...
           createWorld; solveSignature1. 
           apply GenK4RelUT' with (C4:= x6) 
                        (CK:=[])
                        (CN:=x);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         apply seqNtoSeq in H19.
               refine (WeakTheory _ _ H19)...
               apply TheoryEmb1. 
           
           simpl.
           assert (M=[]).
            apply FocusingBangPar in H10...
          sauto. 
          apply map_eq_nil in H4, H9...
           apply FocusingTensor in H13...
           assert(IsPositiveAtomFormulaL x3) by OLSolve.
           assert(IsPositiveAtomFormulaL x5) by OLSolve. 
           specialize (posDestruct' H4) as HC...
           specialize (posDestruct' H9) as HC...
           
           LLTensor; LLRelease;LLStore. 
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: rewrite app_assoc_reverse.
           1-2: rewrite <- H5.
           1-2: rewrite H13.
           1: LLPerm (x5++ u| F1 | :: x3).
           2: LLPerm (x3++ d| G | :: x5).
           1: refine (LinearToClassic2 _ _ _ _ _ _ H16 _)...
           2: refine (LinearToClassic2 _ _ _ _ _ _ H14 _)...
           1-2: apply weakeningGen...
           1-2: apply weakeningGen...
           LLPerm ([]++(u| F1 | :: x3)).
           applyCutC Hi H11.
           LLPerm ([]++(d| G | :: x5)).
           applyCutC Hi H15.        }
                apply FocusingTensor in H13...
                specialize (posDestruct' isFM) as HC...
                refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
                TFocus (BinBipole (IMP_BODY a) Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen;solveSignature1...
                apply weakeningGen;solveSignature1... 
                solveLL.
                LLTensor x5 x6.
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite !secCEncode.
                1,2: rewrite app_assoc_reverse.
                1,2: rewrite <- H5. 
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
- (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             TFocus (RINIT OO).
             LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                rewrite Permutation_app_comm...
                simpl.
                apply NegF with (a:=loc)...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
             specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                checkPermutationCases H12.
                specialize (posDestruct' isFM) as HC...
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H7.
                rewrite H12.
                TFocus (NEG (t_bin IMP F1 G) loc).
                inversion H4. 
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H12.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
                 specialize (posDestruct' isFM) as HC...
               rewrite <- (app_nil_r M).
             refine (LinearToClassic2 _ _ _ _ _ _ H5 _)...
             apply weakeningGen;solveSignature1...
             apply weakeningGen;solveSignature1...  
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H11.
            LLSwapC Hi.
            applyCutC Hi H11.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.
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
            apply allU.
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
            apply allU.  }
      ** (* 2/6 - IMP LEFT *)
      apply BipoleReasoning in H1...
      apply FocusingTensor in H10...
      
      assert(IsPositiveAtomFormulaL x0) by OLSolve.
      rewrite Permutation_app_comm.
      specialize (posDestruct' isFN) as HC...
      refine (LinearToClassic2 _ _ _ _ _ _ H8 _)...
            
      TFocus (BinBipole (IMP_BODY a) Left F1 G). 
      LLTensor [d| t_bin IMP F1 G|] x0.
      simpl...
       LLTensor x2 x3; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: solveSignature1.
      1-2 : rewrite !secCEncode.
      1-2: rewrite app_assoc_reverse.
      1-2: rewrite <- H8.
      applyCutC H9 Hj.
      applyCutC H13 Hj.
      
      checkPermutationCases H12.
      apply FocusingTensor in H10...
      rewrite Permutation_app_comm.
      
      specialize (posDestruct' isFN) as HC...
      refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
      TFocus (BinBipole (IMP_BODY a) Left F1 G). 
      LLTensor (@nil oo) M. 
      apply weakeningGen... 
      apply weakeningGen... solveLL...
      LLTensor x4 x5; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2: solveSignature1.
      1-2 : rewrite !secCEncode.
      1-2: rewrite app_assoc_reverse.
      1-2: rewrite <- H1.
      applyCutC H12 Hj.
      applyCutC H15 Hj.
     
   * (* 3/6 - INIT *) 
   apply FocusingInitRuleU in H1...
   -
   rewrite Permutation_app_comm.
   specialize (posDestruct' isFN) as HC...
   refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
   TFocus (RINIT OO).
   LLTensor [u| OO |] [d| OO |].
   - 
   checkPermutationCases H9.
   rewrite Permutation_app_comm.
   specialize (posDestruct' isFN) as HC...
   refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
   TFocus (RINIT OO).
   LLTensor [u| OO |] (@nil oo).
   apply weakeningGen... 
   apply weakeningGen... solveLL...
   - 
   checkPermutationCases H9.
   simpl... 
   apply PosF with (a:=a)...
   simpl...
   apply seqNtoSeq in Hj.
   refine (WeakTheory _ _ Hj)...
   apply TheoryEmb1. 
   rewrite Permutation_app_comm.
   specialize (posDestruct' isFN) as HC...
   refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
   TFocus (RINIT OO).
   LLTensor (@nil oo) [d| OO |].
   apply weakeningGen... 
   apply weakeningGen... solveLL...
   - 
   checkPermutationCases H7.
   checkPermutationCases H9.
   rewrite H7.
   apply AbsorptionC';solveSignature1...
   rewrite <- H7.
   apply PosF with (a:=a)...
   simpl...
   apply seqNtoSeq in Hj.
   refine (WeakTheory _ _ Hj)...
   apply TheoryEmb1.
   specialize (posDestruct' isFN) as HC...
   rewrite <- (app_nil_r N).
   refine (LinearToClassic2 _ _ _ _ _ _ H1 _)...
   apply weakeningGen... 
   apply weakeningGen... 
   TFocus (RINIT OO).
   LLTensor;solveLL.
   * (* 5/6 - POS *)
      apply BipoleReasoning in H1...
      apply FocusingQuest in H9...
      rewrite H10.
      rewrite <- app_comm_cons.
      apply PosF with (a:=a)...
      simpl.
      eapply weakeningN with (F:=(a, d| OO |)) in Hj...
      LLSwapC H8.
      LLSwapC Hj.
      applyCutC H8 Hj.
      apply allU.
      
      checkPermutationCases H11.
      apply FocusingQuest in H9...
      rewrite H7.
      apply AbsorptionC';solveSignature1...
      rewrite <- H7.
     apply PosF with (a:=a)...
     simpl...
      
      eapply weakeningN with (F:=(a, d| OO |)) in Hj...
      LLSwapC H11.
      LLSwapC Hj.
      applyCutC H11 Hj.
      apply allU.
   * (* 6/6 - NEG *)
      apply BipoleReasoning in H1...
      apply FocusingQuest in H9...
      rewrite H10.
      rewrite <- app_comm_cons.
      apply NegF with (a:=loc)...
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
            apply allU. }
     
      apply FocusingQuest in H9...
      rewrite H7.
      apply AbsorptionC';solveSignature1...
      rewrite <- H7.
     apply NegF with (a:=loc)...
     simpl...
      
      eapply weakeningN with (F:=(loc, u| OO |)) in Hj...
      LLSwapC H11.
      LLSwapC Hj.
      applyCutC H11 Hj.
      apply allU.
   Qed.   
    
Theorem LJCutStepC:
    forall n n' a i j FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true -> 
    m4 a = true ->  
    n' <= n ->
   ( seqN  (LJ a) i ((loc,u|FC|)::L) M  (UP []) -> 
    seqN  (LJ a) j ((a,d|FC|)::L) N  (UP []) ->
    seq   (LJC a (pred n)) L (M++N)  (UP [])).
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
            
        eapply LJCutC with
       (F:=F) (F0:=F0)
       (FC:=FC) (h:=h) (a:=a) (n':=n') (n0:=n0) (n1:=n1)...
  Qed. 
 
Theorem LJCutStep:
    forall n n' a FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true ->
     m4 a = true -> 
    n' <= n ->
   ( seq  (LJ a) L (u|FC|::M)  (UP []) -> 
    seq  (LJ a) L (d|FC|::N)  (UP []) ->
    seq   (LJC a (pred n)) L (M++N)  (UP [])).
  Proof with CutTacPOSNEG.
   intros *.
   intros isFF lngF isFM isFN isFL Ha Ha' Hn'. 
   intros Hi Hj.
   
   apply seqtoSeqN in Hi, Hj...
   eapply AbsorptionL with (i:=loc) in H0...
   eapply AbsorptionL with (i:=a) in H...
   
   eapply LJCutStepC  with
       (FC:=FC) (a:=a) (n':=n') (i:=x0) (j:=x)...
   all: solveSignature1.    
  
  Qed.     
 
 Theorem LJCutAdmissibility:
    forall n h a L M,
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true ->
    m4 a = true -> 
    seqN (LJC a n) h L M (UP []) -> seq (LJ a) L M (UP []) .
    Proof with CutTacPOSNEG.
    
    induction n;induction h using strongind ; intros *; 
    intros isFM isFL mtA m4A HC; try solve[inversion HC].
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
      ++ 
       apply BipoleReasoning in H3...
       simpl in H8.
       apply FocusingBangPar in H7...
       TFocus (BinBipole (IMP_BODY a) Right F0 G).
       LLTensor [u| t_bin IMP F0 G |] (@nil oo).
       simpl. createWorld. solveSignature1.
        apply GenK4RelUT' with (C4:= x2) 
                        (CK:=[])
                        (CN:=x3);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         eapply H in H13...
         srewrite H5 in isFL.
         rewrite map_app in isFL...
         simpl in H7.
       apply FocusingBangPar in H7...
       TFocus (BinBipole (IMP_BODY a) Right F0 G).
       LLTensor.
       solveLL.
       simpl. createWorld. solveSignature1.
        apply GenK4RelUT' with (C4:= x3) 
                        (CK:=[])
                        (CN:=x4);solveSignature1...
         simpl... LLPar. do 2 LLStore.
         eapply H in H14...
         srewrite H7 in isFL.
         rewrite map_app in isFL...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingTensor in H7...
       assert(isx0L: IsPositiveAtomFormulaL x0).
       OLSolve.
       TFocus (BinBipole (IMP_BODY a) Left F0 G).
       LLTensor [d| t_bin IMP F0 G |] x0.
       simpl. LLTensor x2 x3.
       1-2: LLRelease. 
       1-2: LLStore.
       eapply H in H6...
       eapply H in H10...
       
       simpl in H7.
       apply FocusingTensor in H7...
       TFocus (BinBipole (IMP_BODY a) Left F0 G).
       LLTensor (@nil oo) M.
       simpl. solveLL. 
       simpl. LLTensor x3 x4.
       1-2: LLRelease. 
       1-2: LLStore.
       eapply H in H7...
       eapply H in H11...
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
      (* POS *)
       apply BipoleReasoning in H3...
       inversion H6...
       inversion H10...
       2: solveF.
       TFocus (POS OO a). 
       LLTensor [d| OO|] x0.
       LLRelease. LLStoreC.
       eapply H in H11...
       
       inversion H6...
       inversion H11...
       2: solveF.
       TFocus (POS OO a). 
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
       
       assert(seq (LJC a (pred ((S n)))) L (x1 ++ x0) (UP [])).
       refine (LJCutStep _ H7 _ _ _ _ _ _ H11 H5)...
       simpl in H3.
       apply seqtoSeqN in H3...
       eapply IHn in H3...
       2-3: OLSolve.
       LLExact H3.
 Qed.
 
End LJCut.