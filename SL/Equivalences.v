Require Export MMLL.Misc.Hybrid.
Require Export MMLL.SL.FLLTactics.
Require Import Lia.
Require Import MMLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export MMLL.SL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section Equiv.
Context `{SI : Signature}.
  Context `{OLS: OLSig}.
 
  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).
 
  
 Example Oplus1 n B L F G : n |--- B ; L ; DW (F op G) <-> n |--- B ; L ; DW (G op F).
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
   Qed.
   
   Example Oplus2 n B L F: n |--- B ; L ; DW (F op F) -> n |--- B ; L ; DW (F).
   Proof with sauto;solveLinearLogic.
    intros.
    inversion H... 
   Qed.
   
   Example Oplus3 n B L F: n |--- B ; L ; DW (F op zero) -> n |---  B ; L ; DW (F).
   Proof with sauto;solveLinearLogic.
    intros.
    inversion H... 
   Qed.
   
   Example Oplus4 n B L F G H: n |--- B ; L ; DW (F op (G op H)) -> exists m, n <= S m /\ m |--- B ; L ; DW ((F op G) op H).
   Proof with sauto;solveLinearLogic.
   intros.
   inversion H0...
   exists (S (S n0))...
   inversion H5...
   exists (S (S n))...
   exists ((S n))...
   Qed.
  
   Example Tensor1 B L F G : |-- B ; L ; DW (F ** G) <-> |-- B ; L ; DW (G ** F).
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
    tensor N M D B0...
    rewrite H2... 
    rewrite H5... 
    tensor N M D B0 .
    rewrite H2... 
    rewrite H5...
   Qed.
   
  Lemma simplUnb1 BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetU B -> Permutation BD D.
  Proof.   
  intros.
  rewrite (SetU_then_empty H2) in H1.
  rewrite (cxtDestruct BD).
  rewrite H0.
  rewrite H1.
  simpl. 
  rewrite <- cxtDestruct;auto.
  Qed.
 
  Lemma simplUnb2 BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetU D -> Permutation BD B.
  Proof.   
  intros.
  rewrite (SetU_then_empty H2) in H1.
  rewrite (cxtDestruct BD).
  rewrite H.
  rewrite H1.
  rewrite app_nil_r. 
  rewrite <- cxtDestruct;auto.
  Qed.

 
   Example Tensor2 B L F: |-- B ; L ; DW (F ** one) <-> |-- B ; L ; DW (F).
   Proof with sauto;solveLinearLogic.
    split;intros.
    * inversion H...
      inversion H9...
      apply simplUnb2 in H5;auto.
      rewrite H2.
      rewrite H5...
    * tensor L (@nil oo) B (getU B).
      CleanContext.
   Qed.   
      
   Example Tensor3 B L F: |-- B ; L ; DW (F ** zero) <-> |-- B ; L ; DW (zero).
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
    Qed. 
   
   Example Tensor4 B L F G H: |-- B ; L ; DW (F ** (G ** H)) <-> |-- B ; L ; DW ((F ** G) ** H).
   Proof with sauto;solveLinearLogic.
    split;intros.
    * inversion H0...
      inversion H10...
      tensor (M++M0) N0 (getL B1++getL B0++getU B) D0.
      rewrite H3.
      rewrite H7... 
      CleanContext.
      rewrite H6.
      rewrite H12... 
      tensor M M0 B0 B1.
      CleanContext.
      CleanContext.
    * inversion H0...
      inversion H9...
      tensor M0 (N++N0) B1 (getL D0++getL D++getU B).
      rewrite H3.
      rewrite H7... 
      CleanContext.
      rewrite H6.
      rewrite H12... 
      tensor N0 N D0 D.
      CleanContext.
      CleanContext.
   Qed.

   
   Example With1 B L F G X: |-- B ; L ; UP ((F & G)::X) <-> |-- B ; L ; UP ((G & F)::X).
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
   Qed.
   
   Example With2 B L F X: |-- B ; L ; UP ((F & F)::X)  <-> |-- B ; L ; UP (F::X) .
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
   Qed.
   
   Example With3 B L F X: |-- B ; L ; UP ((F & Top)::X) <-> |-- B ; L ; UP (F::X).
   Proof with sauto;solveLinearLogic.
    split;intros;
    inversion H...
   Qed. 
   
   
   Example With4 B L F G H X: |-- B ; L ; UP ((F & (G & H))::X) <-> |-- B ; L ; UP (((F & G) & H)::X).
   Proof with sauto;solveLinearLogic.
    split;intros.
    * inversion H0...
      inversion H7...
      inversion H7...
    * inversion H0...
      inversion H5...
      inversion H5...
   Qed.
   
   Example TensorOplus B L F G H: |-- B ; L ; DW (F ** (G op H)) <-> |-- B ; L ; DW ((F ** G) op (F ** H)).
   Proof with sauto;solveLinearLogic.
    split;intros.
    * inversion H0...
      inversion H10...
      - oplus1.
        tensor M N B0 D.
      - oplus2.
        tensor M N B0 D.
    * inversion H0...
      inversion H4...
      - tensor M N B0 D...
      - inversion H4...
        tensor M N B0 D...
   Qed.   
 
 Example QuestQuest1 n B L a F X: u a = true -> n |--- B ; L ; UP (a ? F :: X) -> 
  S (S n) |--- B ; L ; UP ((a ? F) $ (a ? F) :: X).
   Proof with sauto;solveLinearLogic.
    intros.
    inversion H0...
    apply weakeningN...
 Qed. 
 
 Example QuestQuest2 n B L a F X: u a = true -> n |--- B ; L ; UP ((a ? F) $ (a ? F) :: X) -> 
  n |--- B ; L ; UP (a ? F :: X).
   Proof with sauto;solveLinearLogic.
    intros.
    inversion H0...
    inversion H5...
    inversion H6...
    eapply @contractionN with (F:=(a, F))...
 Qed. 
 
 End Equiv.
