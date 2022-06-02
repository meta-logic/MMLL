Require Import MMLL.SL.FLLTactics.
Require Import MMLL.SL.CutElimination.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
Context {OLS : OLSig}.
Context {SI : Signature}.

 Variable th : oo -> Prop.

Lemma BipoleReasoning {USI: UnbSignature} n B D F G:   seqN th n B D (DW (MAnd (perp F) G)) -> (exists m M, n = S m /\  seqN th m B M (DW G) /\ Permutation D (atom F :: M)) \/ (exists m i C, n = S m /\ seqN th m B D (DW G) /\ mt i = true /\Permutation ((i,atom F) :: C) B). 
 Proof with sauto.
   intros.
   inversion H...
   2:{ inversion H1. }
   assert(Permutation B B0).
   rewrite (cxtDestruct B).
   rewrite (cxtDestruct B0).
   rewrite (SetU_then_empty B)...
   rewrite (SetU_then_empty B0)...
   apply allSeTU...
   apply allSeTU...
   assert(Permutation B D0).
   rewrite (cxtDestruct B).
   rewrite (cxtDestruct D0).
   rewrite (SetU_then_empty B)...
   rewrite (SetU_then_empty D0)...
   apply allSeTU...
   apply allSeTU...
    rewrite <- H0 in H9.
    rewrite <- H1 in H10.
    clear H0 H1 H3 H4 H5.
    inversion H9... 
    left.
   exists n0.
   exists N...
   right.
   exists n0.
   exists i.
   exists C.
   split...
   rewrite H2...
   inversion H1.
   Qed.

 (* Theorem FocusingClause : forall n B D A F,
     seqN th n B D (DW ((perp A) ** F)) ->
 (exists m N, n = S m /\ Permutation D ((atom A)::N) /\
                seqN th m B N  (DW F)) \/
   (exists m i, n = S m /\ In (i, atom A) B /\
                seqN th m B D  (DW F)).
  Proof with sauto.
  intros.
  InvTriAll.
  - left.
    eexists. exists N...
  - right.
    eexists. 
    split...  HProof.
 Qed.
 *)
  
   
       Lemma FocusingInitRuleU {SIU: UnbSignature} : forall h D A A' B,
      seqN th h B D (DW ((perp A) ⊗ (perp A'))) -> 
      Permutation D [atom A; atom A'] \/ 
      (exists i C, D = [atom A] /\ Permutation ((i, atom A') :: C) B /\ mt i = true  ) \/ 
      (exists i C, D = [atom A'] /\ Permutation ((i, atom A) :: C) B  /\ mt i = true ) \/
      (exists i j C1 C2, Permutation ((i, atom A') :: C1) B /\ Permutation ((j, atom A) :: C2) B /\ mt i = true /\mt j = true /\ D=[]).
  Proof with sauto.
    intros.
    apply BipoleReasoning in H...
    inversion H2...
    2:{ solveF. }
    right. left.
    exists i. exists C.
    split...
    inversion H2...
    right. right. left.
    exists x0. exists x1.
    split...
    right. right. right.
    exists i. exists x0.
    exists C. exists x1.
    split...
    solveF.
  Qed.  
  
  
  (*  Theorem FocusingStruct : forall n D B A,
   seqN th n B D (DW ((perp A) ⊗ (? (atom A)))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom 
   A)::N) /\
                seqN th m (B++[atom A]) N  (UP [] )) \/
    (exists m, n = S (S (S m))  /\ In (atom A) B /\

                seqN th m (B++[(atom A)]) D  (UP [] )).            
   Proof with sauto.
   intros.
   InvTriAll.
   left.
  exists n0. exists N...
  right.
  exists n0... 
  HProof.
 Qed.
 *)
 
 
  Theorem FocusingExists :
    forall n FX D G,
    seqN th n G D (DW (Some FX)) ->
      exists m t , n =  S m /\ proper t /\ uniform_oo FX /\
    seqN th m G D (DW (FX t)).
  Proof with sauto.
    intros.
    inversion H... solveF.
    eexists n0, t.
    split;eauto.
  Qed.
 
  Theorem FocusingQuest :
    forall n a A D G,
    seqN th n G D (DW ((? a) (atom A))) ->
      exists m , n =   S (S m)  /\
                 seqN th m ((a,atom A)::G) D (UP []).
  Proof with sauto.
    intros.
    inversion H...
    inversion H5...
    2: solveF.
    eexists n.
    split;eauto.
  Qed.
 
 
 Theorem FocusingBangPar {Unb: UnbSignature}:
    forall n a A B D G, mt a = true -> m4 a = true ->
    seqN th n G D (DW ((! a) ((atom A) ⅋ ( atom B)))) ->
      exists m C4 CN, n =  S (S (S (S (S m)))) + length C4  /\ D = [] /\ Permutation G (C4++CN) /\ SetK4 C4 /\ SetT C4 /\ LtX a C4 /\
                 seqN th m C4 [atom B; atom A] (UP []).
  Proof with sauto.
    intros.
    inversion H1...
    solveF. solveSignature1.
    eapply InvSubExpPhaseUTK4 in H8... 
    2: apply allU.
    inversion H12...
    inversion H15...
    inversion H19...
    2: solveF.
    
    eexists n, x, x0.
    split;[| split;eauto].
    rewrite <- NatComp in H2...
    lia. Qed.
 
 Theorem FocusingBang {Unb: UnbSignature}:
    forall n a A C D G, mt a = true -> m4 a =true ->
    seqN th n ((loc,C)::G) D (DW (Bang a (atom A ))) ->
      exists m X1 X2, n = S (S (S m)) + length X1 /\ Permutation G (X1++X2) /\ SetT X1 /\ SetK4 X1 /\ LtX a X1 /\ D = [] /\ 
                  ( seqN th m X1 [atom A] (UP [])).
  Proof with sauto.
    intros.
    assert(D=[]).
    { inversion H1... solveF. }
    subst.
    apply InvBangTNLoc in H1...
    inversion H4...
    eexists n0, x, x0.
    split;auto.
    lia.
    split;auto.
    
 Qed.

 Theorem FocusingBangU {Unb: UnbSignature}:
    forall n a A D G, mt a = true -> 
    seqN th n G D (DW (Bang a (atom A ))) ->
      exists m, n = S (S m) /\ D = [] /\ 
                  ( seqN th m G [atom A] (UP [])).
  Proof with sauto.
    intros.
    assert(D=[]).
    { inversion H0... solveF. }
    subst.
    apply InvBangTN in H0...
    inversion H0...
    eexists n0.
    split... 
    lia.
 Qed.

 
 Theorem FocusingBang' {Unb: UnbSignature}:
    forall n a A D G, mt a = true -> m4 a = true ->
    seqN th n G D (DW ((! a) (atom A))) ->
      exists m C4 CN, n = S (S (S m)) + length C4  /\  Permutation G (C4++CN) /\  SetT C4 /\ SetK4 C4 /\ LtX a C4 /\
 D = [] /\                seqN th m C4 [atom A] (UP []).
  Proof with sauto.
    intros.
    inversion H1...
    solveF. solveSignature1.
    eapply InvSubExpPhaseUTK4 in H8... 
    2: apply allU.
    inversion H12...
    
    eexists n, x, x0.
    split;[| split;eauto].
    rewrite <- NatComp in H2...
    lia. Qed.
    
 Theorem FocusingBangSet {Unb: UnbSignature}:
    forall n a A C D G, mt a = true -> m4 a =true ->
    seqN th n (Loc C++G) D (DW (Bang a (atom A ))) ->
      exists m X1 X2, n = S (S (S m)) + length X1 /\ Permutation G (X1++X2) /\ SetT X1 /\ SetK4 X1 /\ LtX a X1 /\ D = [] /\ 
                  ( seqN th m X1 [atom A] (UP [])).
  Proof with sauto.
     induction C;   intros.
    eapply FocusingBang'...
    simpl in H1.
    rewrite Permutation_cons_append in H1.
    rewrite app_assoc_reverse in H1.
    specialize (IHC _ _ H H0 H1)...
    checkPermutationCases H5.
    2: exists x, x0, x2...
    
    rewrite <- Permutation_cons_append in H3.
    rewrite H3 in H6.
    inversion H6...
    solveSignature1.
  Qed.
 
  Theorem FocusingPar :
    forall n A B D G,
    seqN th n G D (DW ((atom A) ⅋ ( atom B))) ->
      exists m , n =  S (S(S(S m)))  /\
                 seqN th m G (atom B::atom A::D) (UP []).
  Proof with sauto.
    intros.
    inversion H...
    inversion H5...
    inversion H6...
    inversion H9...
    eexists n.
    split;eauto.
    inversion H7.
  Qed.
  
  Theorem FocusingPlus:
    forall n A B D G ,
    seqN th n G D (DW ( (atom A) ⊕ (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (atom A ::D) (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 seqN th m G (atom B::D) (UP []) ).
  Proof with sauto.
    intros.
    inversion H...
    inversion H4...
    inversion H6...
    left.
    eexists n0.
    split;eauto.
    inversion H4...
    inversion H6...
    right.
    eexists n0.
    split;eauto.
    inversion H1.
  Qed.
  
  Theorem FocusingWith :
    forall n A B D G,
      seqN th n G D (DW ( (atom A) & (atom B))) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m G (atom A::D) (UP []) ) /\
                   (seqN th m G (atom B::D) (UP []) )) .
  Proof with sauto.
    intros.
    inversion H...
    inversion H5...
    inversion H7...
    inversion H9...
    eexists n0.
    split;eauto.
    solveF.
  Qed.
  
  Theorem FocusingTensor {USI: UnbSignature}:
    forall n A B D G,
      seqN th n G D (DW ( (atom A) ⊗ (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( seqN th m G (atom A::M) (UP [])) /\
                  ( seqN th m G (atom B::N) (UP [])).
   Proof with sauto.
    intros.
    inversion H...
    2:{ inversion H1. }
   assert(Permutation G B0).
   rewrite (cxtDestruct G).
   rewrite (cxtDestruct B0).
   rewrite (SetU_then_empty G)...
   rewrite (SetU_then_empty B0)...
   apply allSeTU...
   apply allSeTU...
   assert(Permutation G D0).
   rewrite (cxtDestruct G).
   rewrite (cxtDestruct D0).
   rewrite (SetU_then_empty G)...
   rewrite (SetU_then_empty D0)...
   apply allSeTU...
   apply allSeTU...
   
   rewrite <- H0 in H9.
   rewrite <- H1 in H10.
   
    inversion H9...
    inversion H10...
    inversion H13...
    inversion H15...
    eexists n0, M, N.
    split;eauto.
  Qed.
 
 Theorem FocusingTensorC {USI: UnbSignature}:
    forall n a b A B D G,
      seqN th n G D (DW ( Quest a (atom A) ⊗ Quest b (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( seqN th m ((a,atom A)::G) M (UP [])) /\
                  ( seqN th m ((b,atom B)::G) N (UP [])).
   Proof with sauto.
    intros.
    inversion H...
    2:{ inversion H1. }
   assert(Permutation G B0).
   rewrite (cxtDestruct G).
   rewrite (cxtDestruct B0).
   rewrite (SetU_then_empty G)...
   rewrite (SetU_then_empty B0)...
   apply allSeTU...
   apply allSeTU...
   assert(Permutation G D0).
   rewrite (cxtDestruct G).
   rewrite (cxtDestruct D0).
   rewrite (SetU_then_empty G)...
   rewrite (SetU_then_empty D0)...
   apply allSeTU...
   apply allSeTU...
   
   rewrite <- H0 in H9.
   rewrite <- H1 in H10.
   
    inversion H9...
    inversion H10...
    inversion H13...
    inversion H15...
    eexists n0, M, N.
    split;eauto. solveF. solveF.
  Qed.
 
   Theorem FocusingClauseL {USI: UnbSignature}: forall B D A F,
     seq th B D (DW F) -> seq th B  (atom A::D) (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   LLTensor [atom A] D.
   Qed.  

 Theorem FocusingClauseL'  {USI: UnbSignature}: forall B D D' A F,
   Permutation D (atom A::D') -> seq th B D' (DW F) -> seq th B  D (DW ((perp A) ⊗ F)).
   Proof with auto using FocusingClauseL.
   intros.
   rewrite H...
  Qed. 

     
   Theorem FocusingClauseC  {USI: UnbSignature}: forall i B D A F, mt i = true ->
   In (i, atom A) B ->  seq th B D (DW F) -> seq th B  D (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   rewrite <- (app_nil_l D).
   apply InPermutation in H0...
   LLTensor (nil (A:=oo)) D.
   init2 i x.
   Qed.  

End FLLReasoning.
