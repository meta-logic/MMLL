Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.LNSg.LKBipoles.
Import MMLL.Misc.Permutations.
Require Import MMLL.SL.FLLReasoning.
Require Import MMLL.SL.InvPositivePhase.
         
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section LKCut.

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
    (seqN (LK a) i ((a,u|FC|)::L) M (UP []) ->
     seqN (LK a) j ((a,d|FC|)::L) N (UP []) -> 
     seq (LKC a (pred n)) L (M ++ N) (UP [])).
 
Ltac CutTacPOSNEG := sauto;
  try
    match goal with
    | [ |- isFormula _] => constructor;auto
    | [ |- IsPositiveAtomFormula _] =>  constructor;auto
    | [ |- LKC _ _] => autounfold; solve[constructor;constructor;auto]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
      solve [apply PositiveAtomIn in H';auto;contradiction]
    | [ H: seqN _ _ _ _ (DW zero) |- _] => invTri H
    | [ H: seq  _ _ _ (DW zero) |- _] => invTri' H
    | [ |- LKC _ _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [ |- LK _ ]=> autounfold;solve [repeat (constructor;auto)]
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
  
  
Tactic Notation "Bipole"  constr(B) constr(S) constr(FX) :=
    match B with
     | ALL => TFocus (QuBipole ALL_BODY S FX)
     | SOME => TFocus (QuBipole SOME_BODY S FX)
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
      | seqN _ ?l ((?i, u| ?P|)::?L) ?M _  =>
         match type of Hr with
         | seqN _ ?r ((?i, d| ?P|)::?L) ?N _ =>
           let H' := fresh "H" in assert(H' : l + r = l + r) by auto;
           refine(C _ _ _ _ _ _ _ _ _ _  H'  _ _ Hc _ _ _ _ Hl Hr);
           CutTacPOSNEG
          | _ => idtac
          end
     | _ => idtac      
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
          
  Theorem FocusingForallUP :
    forall n th (y: expr con) FX D G, proper y ->
    seqN th n G D (DW (???{ fun x : expr con => u| FX x |})) ->
      exists m , n =  S (S (S m))  /\ seqN th m G (u| FX y |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    solveF.
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split;eauto.
  Qed.
         
   Theorem FocusingForallDW :
    forall n th (y: expr Syntax.con) FX D G, proper y ->
    seqN th n G D (DW (???{ fun x : expr Syntax.con => d| FX x |})) ->
      exists m , n =  S (S (S m))  /\ seqN th m G (d| FX y |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    solveF.
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split;eauto.
  Qed.

   Theorem FocusingExistsUP :
    forall n th FX D G, 
    seqN th n G D (DW (???{ fun x : expr Syntax.con => u| FX x |})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ seqN th m G (u| FX t |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... solveF. 
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.

   Theorem FocusingExistsDW :
    forall n th FX D G, 
    seqN th n G D (DW (???{ fun x : expr Syntax.con => d| FX x |})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ seqN th m G (d| FX t |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... solveF. 
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.

               
 Ltac permuteALLRight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ?N (u| t_quant ALL ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole ALL_BODY Right FX);
      simpl;
      LLTensor [u| t_quant ALL FX | ] (M++x);
       [  rewrite Hpp;sauto |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallUP _ Hpro H) as Hj';sauto
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ((?i, u| t_quant ALL ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole ALL_BODY Right FX);
      simpl;
      LLTensor (@nil oo) (M++N);
       [  solveLL |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallUP _ Hpro H) as Hj';sauto
       end
      end.
    
 Ltac permuteALLLeft :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ?N (d| t_quant ALL ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsDW in H;sauto; 
        TFocus (QuBipole ALL_BODY Left FX); 
        simpl;
        LLTensor [d| t_quant ALL FX | ] (M++x);[
        rewrite Hpp;sauto |  ] ; match goal with
      [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ((?i, d| t_quant ALL ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsDW in H;sauto; 
        TFocus (QuBipole ALL_BODY Left FX); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  ]; match goal with
       [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
  end.

 Ltac permuteSOMERight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ?N (u| t_quant SOME ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsUP in H;sauto; 
        TFocus (QuBipole SOME_BODY Right FX); 
        simpl;
        LLTensor [u| t_quant SOME FX | ] (M++x);[
        rewrite Hpp;sauto |  ] ; match goal with
      [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ((?i, u| t_quant SOME ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsUP in H;sauto; 
        TFocus (QuBipole SOME_BODY Right FX); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  ]; match goal with
       [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
  end.
        
   Ltac permuteSOMELeft :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ?N (d| t_quant SOME ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole SOME_BODY Left FX);
      simpl;
      LLTensor [d| t_quant SOME FX | ] (M++x);
       [  rewrite Hpp;sauto |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallDW _ Hpro H) as Hj';sauto
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ((?i, d| t_quant SOME ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole SOME_BODY Left FX);
      simpl;
      LLTensor (@nil oo) (M++N);
       [  solveLL |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallDW _ Hpro H) as Hj';sauto
       end
      end.
      
  Context  {USI:UnbSignature}.
  Context  {UND:UnbNoDSignature}.
  
Ltac FocusClause C L A B:=
     match C with
     | AND => match L with
                      | up => TFocus (BinBipole AND_BODY Right A B)
                      | down => TFocus (BinBipole AND_BODY Left A B)
                      end
     | OR => match L with
                      | up => TFocus (BinBipole OR_BODY Right A B)
                      | down => TFocus (BinBipole OR_BODY Left A B)
                      end
     | IMP => match L with
                      | up => TFocus (BinBipole IMP_BODY Right A B)
                      | down => TFocus (BinBipole IMP_BODY Left A B)
                      end
    end.
    
Ltac permute := 
match goal with
 | [ H : Permutation ?M (atom (?a (t_bin ?C ?A ?B)) :: ?x) |- 
       seq _ _ (?M ++ ?N) _] => FocusClause C a A B
 | [ H : Permutation ?N (atom (?a (t_bin ?C ?A ?B)) :: ?x) |- 
       seq _ _ (?M ++ ?N) _] => FocusClause C a A B
 end.
 
 Ltac solveQF :=
  match goal with
   [ H1 : isOLFormula (t_quant qt ?FX), 
     H2 : proper ?x |- isOLFormula (?FX ?x)] =>
                inversion H1;subst;OLSolve;
                match goal with
       [ H : lbind 0%nat _ = lbind 0%nat ?FX |-
          isOLFormula (?FX ?x)] =>
                apply lbindEq in H;sauto;
               try rewrite <- H;sauto
              end  
                
   end.  
  
  Lemma LKCutC F F0 FC L M N a h n0 n1 n' n:
     mt a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutC h a ->
     seqN (LK a) (S n0) ((a,u| FC |) :: L) M (UP []) ->
     seqN (LK a) (S n1) ((a,d| FC |) :: L) N (UP []) ->
     LK a F ->
     ~ IsPositiveAtom F ->
     seqN (LK a) n0 ((a,u| FC |) :: L) M (DW F) ->
     LK a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (LK a) n1 ((a,d| FC |) :: L) N (DW F0) ->
     seq (LKC a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros H4 Heqh isFFC lngF HRel isFM isFN isFL. 
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
      {   (** FF Right is pal *)
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
     3:{ 
      apply BipoleReasoning in H5...
      inversion H12...
      solveF.
      inversion H12...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H13...
      simpl. solveLL.
      checkPermutationCases H14.
      Bipole FF Left.
      LLTensor (@nil oo) (M++N). 
      solveLL... 
      simpl. solveLL. }
     2:{ 
      apply BipoleReasoning in H5...
      inversion H11...
      solveF.
      inversion H11...
      solveF. }
      
      apply BipoleReasoning in H5...
      Bipole TT Right.
      LLTensor [u| t_cons TT |] (M++x1).
      rewrite H7...
      simpl...       
                 checkPermutationCases H8.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDRight.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole AND_BODY Right F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDLeft.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole AND_BODY Left F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORRight.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole OR_BODY Right F G).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.           
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORLeft.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole OR_BODY Left F G).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H11.
    OLSolve.
   checkPermutationCases H14. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H14.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H12...
                simpl in H13.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H11.
                applyCutC Hi H15.
                
                checkPermutationCases H14.
                apply FocusingTensor in H12...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H14.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H11.
                clear H8.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H11.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H11.
                checkPermutationCases H5.
                rewrite H11.
                TFocus (NEG (t_cons TT) a).
                inversion H4...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H11.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
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
      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      TFocus (BinBipole AND_BODY Right F1 G). 
      LLTensor [u| t_bin AND F1 G|] x0.
      simpl. LLRelease. LLWith.
      1-2: LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
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
      inversion H12...
      solveF.
      inversion H12...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H13...
      simpl. solveLL.
      checkPermutationCases H14.
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
      rewrite H13...
      simpl...       
                 checkPermutationCases H14.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDRight.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole AND_BODY Right F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDLeft.
                applyCutC Hi H11.
                applyCutC Hi H11.
                checkPermutationCases H14.
                 
           { clear H13.
                    
           apply @PosNegSetT' with (a:=a)...
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
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite app_comm_cons. 
           applyCutC H9 Hj.
           applyCutC H10 Hj. 
           
           simpl.
           apply FocusingWith in H10...
           apply FocusingPlus in H12...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.  
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle.
           1-2: applyCutC Hi H8. }

                apply FocusingPlus in H12...
                all:TFocus (BinBipole AND_BODY Left F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORRight.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole OR_BODY Right F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.           
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORLeft.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole OR_BODY Left F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H11.
    OLSolve.
   checkPermutationCases H14. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H14.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H12...
                simpl in H13.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H11.
                applyCutC Hi H15.
                
                checkPermutationCases H14.
                apply FocusingTensor in H12...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H14.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H11.
                clear H8.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H11.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H11.
                checkPermutationCases H5.
                rewrite H11.
                TFocus (NEG (t_bin AND F1 G) a).
                inversion H4...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H11.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
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
      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole AND_BODY Left F1 G). 
      1-2: LLTensor [d| t_bin AND F1 G|] x0.
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
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
      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      apply FocusingPlus in H10...
      1-2: TFocus (BinBipole OR_BODY Right F1 G). 
      1-2: LLTensor [u| t_bin OR F1 G|] x0.
      1: simpl; LLPlusL; LLRelease; LLStore.
      2: simpl; LLPlusR; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
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
      inversion H12...
      solveF.
      inversion H12...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H13...
      simpl. solveLL.
      checkPermutationCases H14.
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
      rewrite H13...
      simpl...       
                 checkPermutationCases H14.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDRight.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole AND_BODY Right F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDLeft.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole AND_BODY Left F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORRight.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole OR_BODY Right F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.           
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORLeft.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.

           { clear H13.
                    
           apply @PosNegSetT' with (a:=a)...
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
           apply FocusingWith in H12...
           apply FocusingPlus in H10...
           1: LLPlusL; LLRelease; LLStore. 
           2: LLPlusR; LLRelease; LLStore.  
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite app_comm_cons. 
           1-2: applyCutC H8 Hj.
           
           simpl.
           apply FocusingWith in H12...
           LLRelease. 
           LLWith. 
           1-2: LLStore.
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle. 
           applyCutC Hi H9.
           applyCutC Hi H12.        }                
                
                apply FocusingWith in H12...
                TFocus (BinBipole OR_BODY Left F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H11.
    OLSolve.
   checkPermutationCases H14. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H14.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H12...
                simpl in H13.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H11.
                applyCutC Hi H15.
                
                checkPermutationCases H14.
                apply FocusingTensor in H12...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H14.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H11.
                clear H8.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H11.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H11.
                checkPermutationCases H5.
                rewrite H11.
                TFocus (NEG (t_bin OR F1 G) a).
                inversion H4...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H11.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
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
      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      TFocus (BinBipole OR_BODY Left F1 G). 
      LLTensor [d| t_bin OR F1 G|] x0.
      simpl. LLRelease. LLWith.
      1-2: LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
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
      ** (* 5/6 - IMP Right *)
      apply BipoleReasoning in H1...
      apply FocusingPar in H10...
      TFocus (BinBipole IMP_BODY Right F1 G).
      LLTensor [u| t_bin IMP F1 G |] (x0++N).
      rewrite H11...
      simpl. LLRelease. LLPar. do 2 LLStore.
      do 2 rewrite app_comm_cons.
      applyCutC H9 Hj.
      OLSolve.
      
      checkPermutationCases H12.
      { (** IMP Right is principal *)
          clear H11.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
3:{ 
      apply BipoleReasoning in H5...
      inversion H12...
      solveF.
      inversion H12...
      solveF. }
    3:{
      apply BipoleReasoning in H5...
      Bipole FF Left.
      LLTensor [d| t_cons FF | ] (M++x1).
      rewrite H13...
      simpl. solveLL.
      checkPermutationCases H14.
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
      rewrite H13...
      simpl...       
                 checkPermutationCases H14.  
                Bipole TT Right.
                LLTensor (@nil oo) (M++N).
                solveLL... 
                simpl...
              
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDRight.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole AND_BODY Right F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteANDLeft.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole AND_BODY Left F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                1-2: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORRight.
                applyCutC Hi H11.
                applyCutC Hi H11.
                 checkPermutationCases H14.
                apply FocusingPlus in H12...
                all:TFocus (BinBipole OR_BODY Right F G0).
                all:LLTensor (@nil oo) (M++N).
                all:solveLL...
                all: simpl.
                1: LLPlusL; LLRelease; LLStore.
                2: LLPlusR; LLRelease; LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.
                rewrite <- Permutation_midle.
                applyCutC Hi H14.           
            -- apply BipoleReasoning in H5...
                simpl in H13.
                permuteORLeft.
                applyCutC Hi H12.
                applyCutC Hi H14.
                checkPermutationCases H14.
                apply FocusingWith in H12...
                TFocus (BinBipole OR_BODY Left F G0).
                LLTensor (@nil oo) (M++N).
                solveLL...
                simpl.
                LLRelease. LLWith. 1-2: LLStore.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
            -- apply BipoleReasoning in H5...
                simpl in H13.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H11.
    OLSolve.
   checkPermutationCases H14. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H14.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H12...
                simpl in H13.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H11.
                applyCutC Hi H15.
                
                checkPermutationCases H14.
 
           { clear H13.
                    
           apply @PosNegSetT' with (a:=a)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           eapply GeneralCut' with (C:=dual ((IMP_BODY.(rb_leftBody) F1 G)))...
           rewrite <- (app_nil_r []).
           eapply GeneralCut' with (C:=dual ((IMP_BODY.(rb_rightBody) F1 G)))...
             
           inversion lngF...
           eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
           intros.
           apply TheoryEmb2.
           refine(CuteRuleN H5 _)...
           apply weakeningAll...
                    
           apply IMP_CUTCOHERENT... 
           
           simpl.
           apply FocusingPar in H10...
           LLRelease; LLPar.
           do 2 LLStore. 
           apply AbsorptionLSet'...
           apply setTCEncode...
           apply AbsorptionLSet'...
           apply setTCEncode...
           rewrite !secCEncode.
           simpl; do 2 rewrite app_comm_cons. 
           applyCutC H8 Hj.
           
           simpl.
           apply FocusingTensor in H12...
           LLTensor; LLRelease;LLStore. 
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: srewrite H9; rewrite map_app.
           1-2: rewrite app_assoc_reverse.
          
           1: rewrite Permutation_app_swap_app.
           1-2: apply weakeningGen...
           
           1-2: apply AbsorptionLSet'...
           1,3: apply setTCEncode...
           1-2: rewrite !secCEncode.
           1-2: simpl; rewrite <- Permutation_midle. 
           applyCutC Hi H8.
           applyCutC Hi H13.        }                  
              
                apply FocusingTensor in H12...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H14.
                applyCutC Hi H17.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H11.
                clear H8.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H11.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H11.
                checkPermutationCases H5.
                rewrite H11.
                TFocus (NEG (t_bin IMP F1 G) a).
                inversion H4...
                LLTensor (@nil oo) M;[solveLL | ].
                LLRelease. LLStoreC.
                rewrite <- H11.
               apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H14.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H15.
                solveQF.
                checkPermutationCases H15.
                symmetry in H11.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H17.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            eapply contractionN in H7...
            applyCutC Hi H7.
            apply allU.
            
            apply FocusingQuest in H11...
            TFocus (POS OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H12...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H8.
            LLSwapC Hi.
            applyCutC Hi H8.
            apply allU.
            checkPermutationCases H13.
            apply FocusingQuest in H11...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H13.
            LLSwapC Hi.
            applyCutC Hi H13.
            apply allU.  }
            
            
      apply FocusingPar in H10...
      TFocus (BinBipole IMP_BODY Right F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL...
      LLRelease.
      LLPar. do 2 LLStore.
      do 2 rewrite app_comm_cons.
      applyCutC H12 Hj.
      
      ** (* 2/6 - IMP LEFT *)
      apply BipoleReasoning in H1...
      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      apply FocusingTensor in H10...
      
      assert(IsPositiveAtomFormulaL x0) by OLSolve.
      TFocus (BinBipole IMP_BODY Left F1 G). 
      LLTensor [d| t_bin IMP F1 G|] x0.
      simpl; LLTensor x2 x3; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2 : rewrite secCEncode.
      applyCutC H9 Hj.
      applyCutC H13 Hj.
      
      checkPermutationCases H12.

      PosNegAll a...
      1-2: intro; intros...
      rewrite CEncodeApp.
      rewrite app_assoc_reverse.
      apply AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
      apply FocusingTensor in H10...
      
      TFocus (BinBipole IMP_BODY Left F1 G). 
      LLTensor (@nil oo) M. 
      apply weakeningGen... solveLL...
      LLTensor x4 x5; LLRelease; LLStore.
      1-2: apply AbsorptionLSet'...
      1,3 : apply setTCEncode...
      1-2 : rewrite secCEncode.
      applyCutC H12 Hj.
      applyCutC H15 Hj.
    
   * (* 3/6 - INIT *) 
   apply FocusingInitRuleU in H1...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a M ++ (CEncode a N ++ L)).      
                 
             apply  AbsorptionLSet'...
             apply setTCEncode...
             rewrite secCEncode.
             TFocus (RINIT OO).
             LLTensor [u| OO |] [d| OO |].
             
                checkPermutationCases H9.
                
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
               
                checkPermutationCases H9.
           
                { clear H8.
                   simpl. 
                   PosNeg a.
                   intro; intros...
                   simpl...
                   apply seqNtoSeq in Hj.
               refine (WeakTheory _ _ Hj)...
               apply TheoryEmb1. }
               
                
                apply WeakPosNeg with (a:=a)...
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
                eapply PosFS with (a:=a)...
                intro;intros...
               apply seqNtoSeq in Hj.
               refine (WeakTheory _ _ Hj)...
               apply TheoryEmb1.
               
               
               rewrite <- (app_nil_l N).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL.
  
   * (* 4/6 - QUANTIFIERS *)  
      inversion H6...
      ** (* 1/4 - ALL Right *)
      apply BipoleReasoning in H1...
      TFocus (QuBipole ALL_BODY Right FX). 
      LLTensor [u| t_quant ALL FX|] (x0++N).
      rewrite H12...
      simpl; LLRelease; LLForall. 
      solveUniform. LLStore.
      apply FocusingForallUP with (y:=x1) in H11...
      rewrite app_comm_cons.
      applyCutC H11 Hj.
      solveQF.
      
      checkPermutationCases H13.
      { (** ALL Right is principal *)
          clear H12.
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
            -- apply BipoleReasoning in H5...
                simpl in H14.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H12.
    OLSolve.
   checkPermutationCases H15. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H15.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H13...
                simpl in H14.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                apply FocusingTensor in H13...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H9.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H5.
      
      rewrite H12.
      rewrite Permutation_cons_append.
      rewrite Permutation_app_comm.
      eapply contractionSet' with (C2:=x4).
      1-2:eauto.
      simpl... 
      rewrite <- H12.
      apply NwgFS with (a:=a)...
      intro;intros...
       apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT (OO)).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL...
        
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
       { clear H15.
       inversion H8...
                    inversion lngF...
                     apply lbindEq in H10...
                     apply lbindEq in H16...
                     apply lbindEq in H17...
                  
           apply @PosNegSetT' with (a:=a)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           eapply GeneralCut' with (C:=dual (ALL_BODY.(rq_leftBody) FX0)). 
          rewrite <- (app_nil_r []).
          eapply GeneralCut' with (C:=dual (ALL_BODY.(rq_rightBody) FX)). 
          
           eapply WeakTheory with (th:=(CUTLN n0)).
                 intros.
                 apply TheoryEmb2.
                 refine(CuteRuleN H5 _)...
                 apply weakeningAll...  
                 apply ALL_CUTCOHERENT...
                 symmetry... 
                 rewrite <- H16...
                 solveUniform. 
                 intros... 
                 solveQF. 
     
           
           simpl.
           solveLL. LLStore.
(*            apply FocusingExistsDW in H14. *)
           eapply FocusingForallUP with (y:=x1) in H11...
          
           apply AbsorptionLSet'...
           apply setTCEncode...
           apply AbsorptionLSet'...
           apply setTCEncode...
           rewrite !secCEncode.
           simpl; rewrite app_comm_cons.
           
    assert(H' : x2 + S (S x0) = x2 + S (S x0)) by auto. 
           refine(CutHC _ _ _ _ _ _ _ _ _ _  H'  _ _ lngF _ _ _ _ H19 Hj);
           CutTacPOSNEG.
        solveQF.   
        
         simpl.
         eapply FocusingExistsDW  in H14...
         LLExists x2.  LLRelease. LLStore.
         
           apply AbsorptionLSet'...
           apply setTCEncode...
           apply AbsorptionLSet'...
           apply setTCEncode...
           rewrite !secCEncode.
           simpl; rewrite <- Permutation_midle.
           
    assert(H' : S (S x) + x1 = S (S x) + x1) by auto. 
           refine(CutHC _ _ _ _ _ _ _ _ _ _  H'  _ _ lngF _ _ _ _ Hi H22);
           CutTacPOSNEG.
        solveQF.   
   }                
                
                symmetry in H12.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H9.
            LLSwapC Hi.
            applyCutC Hi H9.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            eapply contractionN in H8...
            applyCutC Hi H8.
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
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H9.
            LLSwapC Hi.
            applyCutC Hi H9.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.  }
             
      TFocus (QuBipole ALL_BODY Right FX). 
      LLTensor (@nil oo) (M++N).
      solveLL...
      simpl; LLRelease; LLForall. 
      solveUniform. LLStore.
      apply FocusingForallUP with (y:=x3) in H11...
      rewrite app_comm_cons.
      applyCutC H14 Hj.
      solveQF.
      ** (* 2/4 - ALL Left *)
      apply BipoleReasoning in H1...
      TFocus (QuBipole ALL_BODY Left FX). 
      LLTensor [d| t_quant ALL FX|] (x0++N).
      rewrite H12...
      apply FocusingExistsDW in H11...
      
      simpl; LLExists x2; LLRelease;LLStore. 
      rewrite app_comm_cons.
      applyCutC H13 Hj.
      solveQF.
      
      checkPermutationCases H13.
     
      TFocus (QuBipole ALL_BODY Left FX). 
      LLTensor (@nil oo) (M++N).
      solveLL...
      apply FocusingExistsDW in H11...
      simpl; LLExists x4; LLRelease;LLStore. 
      rewrite app_comm_cons.
      applyCutC H15 Hj.
      solveQF.
** (* 3/4 - SOME Right *)
      apply BipoleReasoning in H1...
      TFocus (QuBipole SOME_BODY Right FX). 
      LLTensor [u| t_quant SOME FX|] (x0++N).
      rewrite H12...
      apply FocusingExistsUP in H11...
      
      simpl; LLExists x2; LLRelease;LLStore. 
      rewrite app_comm_cons.
      applyCutC H13 Hj.
      solveQF.
      
      checkPermutationCases H13.
      { (** SOME Right is principal *)
          clear H12.
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
            -- apply BipoleReasoning in H5...
                simpl in H14.
                
      match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
        |- seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G |] (M++x);[
        rewrite H2;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
   end.
    applyCutC Hi H12.
    OLSolve.
   checkPermutationCases H15. 

   match goal with 
    | [ H1 : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        H2 : Permutation ?Cx ((?i, u| t_bin IMP ?F ?G |) :: ?x) 
         |- seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H1;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL;sauto |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
        applyCutC Hi H15.
            
            -- apply BipoleReasoning in H5...
                apply FocusingTensor in H13...
                simpl in H14.
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               assert(IsPositiveAtomFormulaL x1) by OLSolve.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] x1.
                LLTensor x3 x4. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H12.
                applyCutC Hi H16.
                
                checkPermutationCases H15.
                apply FocusingTensor in H13...
                PosNegAll a...
                1-2: intro; intros...
                rewrite CEncodeApp.
                LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
               apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) N.
                apply weakeningGen. 
                apply allSeTU... 
                solveLL.
                LLTensor x5 x6. 
                1-2: LLRelease; LLStore.
                1-2: apply  AbsorptionLSet'...
                1,3: apply setTCEncode...
                1-2: rewrite secCEncode.
                1-2: rewrite Permutation_app_comm.
                applyCutC Hi H15.
                applyCutC Hi H18.
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             PosNegAll a...
             1-2: intro; intros...
             rewrite CEncodeApp.
             LLPerm (CEncode a N ++ (CEncode a M ++ L)).      
                 
              apply  AbsorptionLSet'...
               apply setTCEncode...
               rewrite secCEncode.
               TFocus (RINIT OO).
                LLTensor [u| OO |] [d| OO |].
                checkPermutationCases H12.
                clear H9.
                rewrite Permutation_app_comm...
                simpl.
                PosNeg a.
                intro; intros...
                simpl.
                apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               rewrite Permutation_app_comm.
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor [u| OO |] (@nil oo).
                solveLL.
                
                checkPermutationCases H12.
                rewrite Permutation_app_comm.
                apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT OO).
                LLTensor (@nil oo) [d| OO |] .
                solveLL.
                
                checkPermutationCases H12.
                checkPermutationCases H5.
      
      rewrite H12.
      rewrite Permutation_cons_append.
      rewrite Permutation_app_comm.
      eapply contractionSet' with (C2:=x4).
      1-2:eauto.
      simpl... 
      rewrite <- H12.
      apply NwgFS with (a:=a)...
      intro;intros...
       apply seqNtoSeq in Hi.
               refine (WeakTheory _ _ Hi)...
               apply TheoryEmb1.
               
               rewrite <- (app_nil_l M).
               apply WeakPosNeg with (a:=a)...
               1-2: intro; intros...
               TFocus (RINIT (OO)).
                LLTensor (@nil oo) (@nil oo).
                solveLL. solveLL...
        
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteALLRight.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteALLLeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
                symmetry in H12.
                permuteSOMERight.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
            -- apply BipoleReasoning in H5...
                simpl in H15.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H16.
                solveQF.
                checkPermutationCases H16.
       { clear H15.
       inversion H8...
                    inversion lngF...
                     apply lbindEq in H10...
                     apply lbindEq in H16...
                     apply lbindEq in H17...
                  
           apply @PosNegSetT' with (a:=a)...
           1-2: intro;intros...
           rewrite <- (app_nil_r []).
           
           eapply GeneralCut' with (C:=dual (SOME_BODY.(rq_leftBody) FX0)). 
          rewrite <- (app_nil_r []).
          eapply GeneralCut' with (C:=dual (SOME_BODY.(rq_rightBody) FX)). 
          
           eapply WeakTheory with (th:=(CUTLN n0)).
                 intros.
                 apply TheoryEmb2.
                 refine(CuteRuleN H5 _)...
                 apply weakeningAll...  
                 apply SOME_CUTCOHERENT...
                 symmetry... 
                 rewrite <- H16...
                 solveUniform. 
                 intros... 
                 solveQF. 

         simpl.
         eapply FocusingExistsUP  in H11...
         LLExists x2.  LLRelease. LLStore.
         
           apply AbsorptionLSet'...
           apply setTCEncode...
           apply AbsorptionLSet'...
           apply setTCEncode...
           rewrite !secCEncode.
           simpl; rewrite app_comm_cons.
           
    assert(H' : x1 + S (S x0) = x1 + S (S x0)) by auto. 
           refine(CutHC _ _ _ _ _ _ _ _ _ _  H'  _ _ lngF _ _ _ _ H22 Hj);
           CutTacPOSNEG.
        solveQF.   

           simpl.
           solveLL. LLStore.
           eapply FocusingForallDW with (y:=x1) in H14...
          
           apply AbsorptionLSet'...
           apply setTCEncode...
           apply AbsorptionLSet'...
           apply setTCEncode...
           rewrite !secCEncode.
           simpl; rewrite <- Permutation_midle.
           
    assert(H' : S (S x) + x2 = S (S x) + x2) by auto. 
           refine(CutHC _ _ _ _ _ _ _ _ _ _  H'  _ _ lngF _ _ _ _ Hi H19);
           CutTacPOSNEG.
        solveQF.   
        
   }                
                symmetry in H12.
                permuteSOMELeft.
                rewrite <- Permutation_midle.
                applyCutC Hi H18.
                solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            apply FocusingQuest in H12...
            TFocus (POS OO a).
            LLTensor [d| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, d| OO |)) in Hi...
            LLSwapC H9.
            LLSwapC Hi.
            applyCutC Hi H9.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            eapply contractionN in H8...
            applyCutC Hi H8.
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
            TFocus (NEG OO a).
            LLTensor [u| OO |] (M++x1).
            rewrite H13...
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H9.
            LLSwapC Hi.
            applyCutC Hi H9.
            apply allU.
            checkPermutationCases H14.
            apply FocusingQuest in H12...
            TFocus (NEG OO a).
            LLTensor (@nil oo) (M++N).
            solveLL.
            LLRelease. LLStoreC.
            eapply weakeningN with (F:=(a, u| OO |)) in Hi...
            LLSwapC H14.
            LLSwapC Hi.
            applyCutC Hi H14.
            apply allU.  }
            
      TFocus (QuBipole SOME_BODY Right FX). 
      LLTensor (@nil oo) (M++N).
      solveLL...
      apply FocusingExistsUP in H11...
      simpl; LLExists x4; LLRelease;LLStore. 
      rewrite app_comm_cons.
      applyCutC H15 Hj.
      solveQF.
      ** (* 4/4 - SOME Left *)
      apply BipoleReasoning in H1...
      TFocus (QuBipole SOME_BODY Left FX). 
      LLTensor [d| t_quant SOME FX|] (x0++N).
      rewrite H12...
      simpl; LLRelease; LLForall. 
      solveUniform. LLStore.
      apply FocusingForallDW with (y:=x1) in H11...
      rewrite app_comm_cons.
      applyCutC H11 Hj.
      solveQF.
      
      checkPermutationCases H13.
    
      TFocus (QuBipole SOME_BODY Left FX). 
      LLTensor (@nil oo) (M++N).
      solveLL...
      simpl; LLRelease; LLForall. 
      solveUniform. LLStore.
      apply FocusingForallDW with (y:=x3) in H11...
      rewrite app_comm_cons.
      applyCutC H14 Hj.
      solveQF.
   * (* 5/6 - POS *)
      apply BipoleReasoning in H1...
      apply FocusingQuest in H9...
      rewrite H10.
      rewrite <- app_comm_cons.
      PosNeg a.
      intro; intros...
      simpl.
      eapply weakeningN with (F:=(a, d| OO |)) in Hj...
      LLSwapC H8.
      LLSwapC Hj.
      applyCutC H8 Hj.
      apply allU.
      
      checkPermutationCases H11.
      apply FocusingQuest in H9...
      rewrite H6.
      apply contraction with (F:=(x0, d| OO |))...
      apply allU.
      rewrite <- H6.
      apply PosFS with (a:=a)...
      intro;intros...
      
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
      PosNeg a.
      intro; intros...
      simpl.
      eapply weakeningN with (F:=(a, u| OO |)) in Hj...
      LLSwapC H8.
      LLSwapC Hj.
      applyCutC H8 Hj.
      apply allU.
      
      checkPermutationCases H11.
      { 
       apply FocusingQuest in H9...
        eapply contractionN in H6...
            applyCutC H6 Hj.
            apply allU. 
     }
      
      apply FocusingQuest in H9...
      rewrite H6.
      apply contraction with (F:=(x0, u| OO |))...
      apply allU.
      rewrite <- H6.
      apply NwgFS with (a:=a)...
      intro;intros...
      
      eapply weakeningN with (F:=(a, u| OO |)) in Hj...
      LLSwapC H11.
      LLSwapC Hj.
      applyCutC H11 Hj.
      apply allU.
  Qed.    
  
  
       Lemma LKCutL F F0 FC L M N a h n0 n1 n' n:
     mt a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutC h a -> 
     seqN (LK a) (S n0) L (u| FC | :: M) (UP []) ->
     seqN (LK a) (S n1) L (d| FC | :: N) (UP []) ->
     LK a F ->
     ~ IsPositiveAtom F ->
     seqN (LK a) n0 L (u| FC | :: M) (DW F) ->
     LK a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (LK a) n1 L (d| FC | :: N) (DW F0) ->
     seq (LKC a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros H4 Heqh isFFC lngF HRel isFM isFN isFL. 
    intro CutHC.
    intros Hi Hj.
    intros H H0 H1 H2 H3 H5.

   eapply AbsorptionL with (i:=a) in Hi...
   eapply AbsorptionL with (i:=a) in Hj...
   eapply AbsorptionL with (i:=a) in H1...
   eapply AbsorptionL with (i:=a) in H5...
   
   eapply LKCutC with
       (F:=F) (F0:=F0)
       (FC:=FC) (h:=h) (a:=a) (n':=n') (n0:=n0) (n1:=n1)...
   Qed.    
   
Theorem LKCutStepC:
    forall n n' a i j FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true -> 
    n' <= n ->
   ( seqN  (LK a) i ((a,u|FC|)::L) M  (UP []) -> 
    seqN  (LK a) j ((a,d|FC|)::L) N  (UP []) ->
    seq   (LKC a (pred n)) L (M++N)  (UP [])).
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
         inversion H6.
    - intros HRel i Heqh FC isFFC lngF N isFN M isFM L isFL.
       intros Hi Hj.
       
        assert(CutC h a).
        { unfold CutC;intros.
            revert H11.
            revert H10.
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
            ++ apply InUNotPos in H6;sauto...
            ++ apply RemoveNotPos2 in H6;sauto...
            ++
            
        eapply LKCutC with
       (F:=F) (F0:=F0)
       (FC:=FC) (h:=h) (a:=a) (n':=n') (n0:=n0) (n1:=n1)...
  Qed. 
 
Theorem LKCutStep:
    forall n n' a FC L M N,
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true -> 
    n' <= n ->
   ( seq  (LK a) L (u|FC|::M)  (UP []) -> 
    seq  (LK a) L (d|FC|::N)  (UP []) ->
    seq   (LKC a (pred n)) L (M++N)  (UP [])).
  Proof with CutTacPOSNEG.
   intros *.
   intros isFF lngF isFM isFN isFL Ha Hn'. 
   intros Hi Hj.
   
   apply seqtoSeqN in Hi, Hj...
   eapply AbsorptionL with (i:=a) in H0...
   eapply AbsorptionL with (i:=a) in H...
   
   eapply LKCutStepC  with
       (FC:=FC) (a:=a) (n':=n') (i:=x0) (j:=x)...
  
  Qed.     
 
 Theorem LKCutAdmissibility:
    forall n h a L M,
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL (second L) -> 
    mt a = true -> 
    seqN (LKC a n) h L M (UP []) -> seq (LK a) L M (UP []) .
    Proof with CutTacPOSNEG.
    
    induction n;induction h using strongind ; intros *; 
    intros isFM isFL mtA HC; try solve[inversion HC].
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
       simpl in H7.
       apply FocusingPar in H7...
       TFocus (BinBipole IMP_BODY Right F0 G).
       LLTensor [u| t_bin IMP F0 G |] x0.
       simpl. LLRelease. LLPar. do 2 LLStore.
       eapply H in H6...
       OLSolve.
       
       simpl in H7.
       apply FocusingPar in H7...
       TFocus (BinBipole IMP_BODY Right F0 G).
       LLTensor (@nil oo) M.
       solveLL.
       simpl. LLRelease. LLPar. do 2 LLStore.
       eapply H in H7...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H7.
       apply FocusingTensor in H7...
       assert(isx0L: IsPositiveAtomFormulaL x0).
       OLSolve.
       TFocus (BinBipole IMP_BODY Left F0 G).
       LLTensor [d| t_bin IMP F0 G |] x0.
       simpl. LLTensor x2 x3.
       1-2: LLRelease. 
       1-2: LLStore.
       eapply H in H6...
       eapply H in H10...
       
       simpl in H7.
       apply FocusingTensor in H7...
       TFocus (BinBipole IMP_BODY Left F0 G).
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
      (* Quantifiers *)
      inversion H0...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H8.
       inversion H8...
       inversion H12...
       solveF.
       Bipole ALL Right FX.
      
       LLTensor [u| t_quant ALL FX |] x0.
       simpl. LLRelease. LLForall. 
       specialize (H15 _ H3).
       inversion H15...
       LLStore.
       apply H in H18...
       inversion H5...
       apply lbindEq in H10...
       rewrite <- H10...
       
        simpl in H8.
       inversion H8...
       inversion H13...
       solveF.
      
       Bipole ALL Right FX.
      simpl.
       LLTensor (@nil oo) M. 
       solveLL.
       simpl. LLRelease. LLForall. 
       specialize (H16 _ H3).
       inversion H16...
       LLStore.
       apply H in H19...
       inversion H5...
       apply lbindEq in H11...
       rewrite <- H11...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H8.
       inversion H8...
       solveF.
       inversion H13...
       inversion H15...
       
       Bipole ALL Left FX.
      
       LLTensor [d| t_quant ALL FX |] x0.
       simpl. LLExists t. 
       LLRelease. LLStore.
       apply H in H18...
       inversion H5...
       apply lbindEq in H11...
       rewrite <- H11...
       
        simpl in H8.
       inversion H8...
       solveF.
       inversion H14...
       inversion H16...
      
       Bipole ALL Left FX.
      simpl.
       LLTensor (@nil oo) M. 
       solveLL.
       LLExists t. LLRelease. LLStore.
       apply H in H19...
       inversion H5...
       apply lbindEq in H12...
       rewrite <- H12...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H8.
       inversion H8...
       solveF.
       inversion H13...
       inversion H15...
       
       Bipole SOME Right FX.
      
       LLTensor [u| t_quant SOME FX |] x0.
       simpl. LLExists t. 
       LLRelease. LLStore.
       apply H in H18...
       inversion H5...
       apply lbindEq in H11...
       rewrite <- H11...
       
        simpl in H8.
       inversion H8...
       solveF.
       inversion H14...
       inversion H16...
      
       Bipole SOME Right FX.
      simpl.
       LLTensor (@nil oo) M. 
       solveLL.
       LLExists t. LLRelease. LLStore.
       apply H in H19...
       inversion H5...
       apply lbindEq in H12...
       rewrite <- H12...
      ++ 
       apply BipoleReasoning in H3...
       simpl in H8.
       inversion H8...
       inversion H12...
       solveF.
       Bipole SOME Left FX.
      
       LLTensor [d| t_quant SOME FX |] x0.
       simpl. LLRelease. LLForall. 
       specialize (H15 _ H3).
       inversion H15...
       LLStore.
       apply H in H18...
       inversion H5...
       apply lbindEq in H10...
       rewrite <- H10...
       
        simpl in H8.
       inversion H8...
       inversion H13...
       solveF.
      
       Bipole SOME Left FX.
      simpl.
       LLTensor (@nil oo) M. 
       solveLL.
       simpl. LLRelease. LLForall. 
       specialize (H16 _ H3).
       inversion H16...
       LLStore.
       apply H in H19...
       inversion H5...
       apply lbindEq in H11...
       rewrite <- H11...
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
       TFocus (NEG OO a). 
       LLTensor [u| OO|] x0.
       LLRelease. LLStoreC.
       eapply H in H11...
       
       inversion H6...
       inversion H11...
       2: solveF.
       TFocus (NEG OO a). 
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
       
       assert(seq (LKC a (pred ((S n)))) L (x1 ++ x0) (UP [])).
       refine (LKCutStep _ H7 _ _ _ _ _ H11 H5)...
       simpl in H3.
       apply seqtoSeqN in H3...
       eapply IHn in H3...
       2-3: OLSolve.
       LLExact H3.
 Qed.
 
End LKCut.