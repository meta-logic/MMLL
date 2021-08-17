(** Invertibility lemmas: Positive phase

This file proves some invertibility lemmas showing that positive rules
can be switched.
 *)

Require Export MMLL.Misc.Hybrid.
Require Export MMLL.SL.FLLTactics.
Require Import MMLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export MMLL.SL.InvNegativePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Section Absoroption.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.
         
 Lemma AbsorptionC : forall th n i Gamma Delta F X,
   u i = true -> mt i = true ->  seqN th n ((i,F) :: Gamma) ( F::Delta)  X ->
      seqN th n ((i,F) :: Gamma) Delta  X.
  Proof with sauto.
  do 2 intro.
    induction n using strongind ;intros.
    * inversion H1...
      solveLL.
    * inversion H2;solveF;solveLL...
      + apply PermutationInCons in H4 as H4'.
        apply in_app_or in H4'.
        destruct H4'.
        { apply InPermutation in H3;
          destruct H3.
          rewrite H3 in H4;simpl in H4.
          apply Permutation_cons_inv in H4.
          tensor x N B D.
          LLrewrite H3 in H8.
          LLSplit in H8. 
          CleanContext.
          LLSplit...
          rewrite <- H5.
          rewrite <- H5 in H8.
          CleanContext.
          
      }
      {
        apply InPermutation in H3;
        destruct H3.
        rewrite H3 in H4;simpl in H4.
        rewrite <- perm_takeit_2 in H4.
        apply Permutation_cons_inv in H4.
        tensor M x B D.
        rewrite H3 in H9. 
        rewrite cxtDestruct in H9.
        rewrite <- H6 in H9.
        CleanContext.
        rewrite cxtDestruct.
        rewrite <- H6.
        CleanContext.
      }
    + rewrite perm_swap... apply H... LLExact H4.  
    + apply H... LLExact H5.  
    + apply Remove_Permute in H5... 
      apply PProp_perm_select in H5.
      CleanContext.
      decide2u i F0.
      rewrite H8...
      rewrite H5 in H6. 
      eapply H in H6...
      rewrite H7.
      decide1 F0.
    + inversion H7... 
      { apply H in H8...
        decide2u i0 F0... }
      { apply H in H8...
        decide2u i0 F0... }
    + inversion H7...    
      decide2l i0 F0 ((i, F) :: l2)... 
    + apply H in H6...
      decide3 F0.
    + apply H in H6...
      existential t.
  Qed.


 Lemma AbsorptionL : forall th n i Gamma Delta F X,
   mt i = true ->  seqN th n (Gamma) ( F::Delta)  X ->
      seqN th n ((i,F) :: Gamma) Delta  X.
  Proof with sauto.
  intros.
  destruct (uDec i).
  - apply AbsorptionC...
    apply weakeningN... 
  - 
  revert dependent X.
  revert dependent i.
  revert Gamma Delta F.
    induction n using strongind ;intros.
    * inversion H0...
      solveLL.
    * inversion H1;solveF;solveLL...
      + apply PermutationInCons in H3 as H4'.
        apply in_app_or in H4'.
        destruct H4'.
        { apply InPermutation in H2;
          destruct H2.
          rewrite H2 in H3;simpl in H3.
          apply Permutation_cons_inv in H3.
          tensor x N ((i,F)::B) D.
          CleanContext.
          CleanContext.
          CleanContext.
          rewrite H2 in H7... 
      }
      {
        apply InPermutation in H2;
        destruct H2.
        rewrite H2 in H3;simpl in H3.
        rewrite <- perm_takeit_2 in H3.
        apply Permutation_cons_inv in H3.
        tensor M x B ((i,F)::D).
        CleanContext.
        CleanContext.
        CleanContext.
        rewrite H6... perm.
          rewrite H2 in H8... 
      }
     + rewrite perm_swap...   
    + apply H... LLExact H4.    
    + apply Remove_Permute in H4... 
      apply PProp_perm_select in H4.
      CleanContext.
      decide2l i F0.
      rewrite H7...
      rewrite H4 in H5. 
      rewrite H6.
      decide1 F0.
    + decide2u i0 F0... 
    + inversion H6...    
      decide2l i0 F0 ((i, F) :: B')...
      decide2l i0 F0 ((i, F) :: t':: l2)...
       
    + decide3 F0.
    + existential t.
  Qed.

Lemma AbsorptionCSet : forall th n C Gamma Delta X,
  SetT C -> SetU C -> seqN th n (C++Gamma) (Delta++ (second C))  X ->
      seqN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  destruct a as [i F].
  apply AbsorptionC. 
  SLSolve. SLSolve.
  rewrite Permutation_cons_append.
  rewrite app_assoc_reverse.
  eapply IHC.
  SLSolve. SLSolve.
  LLExact H1...
  perm.
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall th  C Gamma Delta X,
  SetT C ->  SetU C -> seq th (Gamma++C) (Delta++ (second C))  X ->
      seq th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H1...
  rewrite Permutation_app_comm in H1.
  eapply AbsorptionCSet in H1...
  apply seqNtoSeq in H1...
  LLExact H1.
  Qed.
  
 Lemma AbsorptionLSet : forall th n C Gamma Delta X,
  SetT C ->  seqN th n (Gamma) (Delta++ (second C))  X ->
      seqN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  destruct a as [i F].
  apply AbsorptionL.
  SLSolve.
  apply IHC.
  SLSolve.
  LLExact H0...
  perm.
  Qed. 
  
 Lemma AbsorptionLSet_rev : forall th  C Gamma Delta X,
  SetT C ->  seq th (Gamma) (Delta++ (second C))  X ->
      seq th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0...
  apply AbsorptionLSet in H0...
  apply seqNtoSeq in H0...
  LLExact H0.
  Qed.
 
 
End Absoroption.


Section InvPosPhase.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).

  Ltac solveList :=
    match goal with
      [ H : [] = ?M ++ [?F] |- _ ] =>
      symmetry in H; apply app_eq_nil in H;inversion H as [H' H''];inversion H''
    | [ H :  ?M ++ [?F] = [ ] |- _ ] =>
      apply app_eq_nil in H; inversion H as [H' H''];inversion H''
    end.

  Ltac seqPermutation := 
    match goal with
      [ H : Permutation ?M ?T ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite H; auto)
    | [ H : Permutation ?T ?M ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite <- H; auto)  
    end.

  Ltac seqPerm H S := 
    match type of H with
      Permutation ?M ?T => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite H;auto
                           end
    | Permutation ?T ?M => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite <- H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite <- H;auto
                           end                      
    end.   

  Section AbsorptionTheory.

    Theorem AbsorptionPerp :  forall n B M A X , theory (perp A) -> n |--- B; (perp A) ::  M; X -> n |--- B; M; X.
    Proof with solveF.
      induction n;intros ;inversion H0;subst;eauto;clear H0...
      + (* tensor: A+ is in N or in M0 *)
        assert (In (perp A)  ( M0 ++ N)).
        apply Permutation_in with (l:= (perp A) :: M)...
        apply in_app_or in H0;destruct H0.
        ++ (* A+  in H0 *)
          apply InPermutation in H0;destruct H0.
          rewrite H0 in H6.
          apply IHn in H6...
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_inv in H2.
          rewrite H2.
          tensor x N B0 D.
        ++ (* A+ in N *)
          apply InPermutation in H0;destruct H0.
          rewrite H0 in H7.
          apply IHn in H7...
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_app_inv in H2.
          rewrite H2.
          tensor M0 x B0 D.
      + store.
        rewrite perm_swap in H3.
        eapply IHn in H3;auto.
      + (*dec1 *)
        inversion H3;subst;eauto.
    Qed.
   
   Theorem AbsorptionPerp2 :  forall n B M A L , theory (perp A) -> n |--- B; M; UP (L++[perp A]) -> n |--- B; M; (UP L).
    Proof with sauto;solveF.
      intro.
      induction n;intros.
      inversion H0... 
      + apply ListConsApp in H5...
      + inversion H0...
        -  apply ListConsApp in H5...
        - apply ListConsApp in H2...
          apply tri_bot...
          apply IHn with (A:=A)...
        -  apply ListConsApp in H2...
          apply tri_par...
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          apply tri_with...
          apply IHn with (A:=A)...
          apply IHn with (A:=A)...   
        - apply ListConsApp in H2...
          apply tri_quest...
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          CleanContext.
          eapply AbsorptionPerp with (A:=A)...
          eapply HeightGeqLEx.
          2:{ exact H6. }
          perm. lia.
          store.
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          apply tri_fx;intros...
          apply H6 in H1.
          apply IHn with (A:=A)...
    Qed.      
    
   Theorem AbsorptionPerp' :  forall B M A L , theory (perp A) -> |-- B; M; UP (L++[perp A]) -> |-- B; M; (UP L).
    Proof with auto.
   intros.
   apply seqtoSeqN in H0.
   destruct H0.
   apply  AbsorptionPerp2 in H0...
   apply seqNtoSeq in H0...
   Qed.
      
          
       
    Lemma app_eq_unit_sym : forall (A : Type) (y : list A) (a b : A),
        [a] = y ++ [b] -> y = [] /\ b = a.
    Proof.
       intros.
       symmetry in H.
      apply app_eq_unit in H.
      destruct H. 
      inversion H. inversion H1.
      firstorder.
      inversion H. inversion H1. Qed.
      
    Definition RUpTheory (n:nat) := forall B L  F  M , 
        theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F ->
        n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).

    Definition RDownTheory (n:nat) := forall B  F  M  H, 
         ~ asynchronous F ->  ~ IsPositiveAtom F -> ~ IsNegativeAtom F -> theory F -> 
        n |--- B ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RIndTheory (n:nat) := RUpTheory n /\ RDownTheory (n -1). 

    Lemma RDownTheory0 : RDownTheory 0.
    Proof with sauto.
      unfold RDownTheory. intros B F M H FNA FNP FNN FT HD.
      inversion HD... 
       solveF. 
    Qed.

    Lemma RUpTheory0 : RUpTheory 0.
    Proof with subst;auto.
      unfold RUpTheory. intros B L F M FT FNP FNN HD.
      destruct L.
      + inversion HD...
        decide3 top.
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUpTheory *)
    (* =============================================== *)   

    Theorem InvTheoryUP: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RUpTheory (S n).
    Proof with subst;auto;solveF;solveLL.
      intros n IH.
      unfold RUpTheory.
      intros B L1 F M1 FT FNA FNN HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
          decide3 top. 
        ++ 
          apply seqNtoSeq in H3;auto. 
        ++ 
          decide3 (F0 $ G). 
          apply seqNtoSeq in H3;auto. 
        ++ 
          decide3 (F0 & G). 
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          decide3 (i ? F0).
          apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RIndTheory n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        *
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M1) in H0;[|perm].
          do 2 destruct H0.
          inversion H0;subst.
          **
            decide3 F.
            apply seqNtoSeq in H1;auto.
            rewrite H2;auto.
          **   
            eapply tri_dec1' with (F1:= F0) (L'0:=l2);auto.
            eapply HDown with (F:= F);auto.
            simpl; rewrite Nat.sub_0_r.
            eapply exchangeLCN with (LC:=F :: l2)...
            rewrite H2... 
        *
          decide2u i F0. 
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
        *
          decide2l i F0 B'. 
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
        
        *
          decide3 F0 ...
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
          ++ 
           decide3 (F{ FX}) ...
            generalize (H5 x);intros.
            apply H in properX .
            apply seqNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndTheory n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        all: eapply HUp with (F:=F);auto. 
        generalize (H5 x properX);intros...
    Qed.

    (* =============================================== *)
    (* PROOF OF RDownTheory *)
    (* =============================================== *)   

    Theorem InvTheoryDW: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RDownTheory (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDownTheory.  intros B F M H FNA FNP FNN FT HD1.
      inversion HD1;subst ... 
      +
        checkPermutationCases  H1.
        ++
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
         
          assert(n0 |--- B0; (F::x); (>> F0)).
          seqPerm H0 H5. 
(*           apply HDown in H... *)
          tensor x N B0 D.  
          apply HDown in H... 
          apply seqNtoSeq in H9;auto.
        ++
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- D; (F::x); (>> G)).
          seqPerm H0 H9. 

          apply HDown in H...

          tensor M0 x B0 D.   
       
          apply seqNtoSeq in H5;auto.
      +
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H4 ...
      + 
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H4 ... 
      + rewrite Permutation_cons_append in H5.
        eapply UpExtension in H5...
        assert(HRI: RIndTheory x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H3 ...
      +
        assert(HRI: RIndTheory (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H6 ...
        existential t.
    Qed.

    Theorem InvAuxTheory : forall n, RIndTheory n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTheory.
        split; [apply RUpTheory0 | apply RDownTheory0].
      + unfold RIndTheory in *.
        split;[|simpl; rewrite Nat.sub_0_r].
        apply InvTheoryUP; assumption.
        apply InvTheoryDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionTheory : forall B L F  M,   
        theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F  -> 
        |-- B ; M ; UP (L++[F]) -> |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpTheory n) by (apply InvAuxTheory).
      apply seqtoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros.
      eapply H3;eauto.
    Qed.

  End AbsorptionTheory.


  Section AbsorptionClassic.

    Definition RUp (n:nat) := forall i B L  F  M , 
      u i = true -> mt i = true -> In (i,F) B -> n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).  

    Definition RDown (n:nat) := forall i B F  M  H, 
        ~ asynchronous F ->
    u i = true ->  mt i = true -> In (i,F) B -> n |--- B ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

    Lemma RDown0 : RDown 0.
    Proof with sauto;solveLL.
      unfold RDown. intros i B F M H FNA U MT FB HD.
      inversion HD...
    Qed.

    Lemma RUp0 : RUp 0.
    Proof with subst;auto;solveLL.
      unfold RUp. intros i B L F M U MT FB HD.
      destruct L.
      + inversion HD...
        decide2u i top.
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvCopyUP: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RUp. intros i B L1 F M U MT FB HD.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD... 
        ++
        decide2u i top.
        ++ 
          apply seqNtoSeq in H3;auto. 
        ++
        decide2u i (F0 $ G).
        apply seqNtoSeq in H3;auto.
        ++ 
          decide2u i (F0 & G). 
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          decide2u i (i0 ? F0). 
          apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M) in H0;[|perm].
          CleanContext.
          inversion H2;subst.
          **
            decide2u i F. 
            apply seqNtoSeq in H1;auto.
            rewrite H3;auto.
          **    
            decide1 F0 l2. 
            eapply HDown with (F:= F) (i:=i);auto.
            
            eapply exchangeLCN with (LC:=F :: l2)...
            seqPerm H3 H1...
        *
          decide2u i0 F0.
            eapply HDown with (F:= F) (i:=i);auto.
            
        * assert(In (i, F) ((i0, F0) :: B')).
          apply Remove_Permute in H2;auto.
          rewrite H2 in FB;auto.
          inversion H6...
           decide2l i0 F0 B'.
           eapply HDown with (F:= F) (i:=i);auto.
        *
          decide3 F0. 
          eapply HDown with (F:= F) (i:=i);auto.
          ++ 
            decide2u i (F{ FX}). 
            generalize (H5 x);intro.
            apply H in properX.
            apply seqNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        all: eapply HUp with (F:=F) (i:=i);auto.
        intuition.   
        generalize (H5 x properX);intros...
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   

    Theorem InvCopyDW: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDown.  intros i B F M H FNA U MT FB HD.
      inversion HD...
       apply InPermutation in FB...
      
      + 
        checkPermutationCases H1.
        ++ 
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0; F::x0; (>> F0)).
          seqPerm H1 H5.

          eapply HDown in H0...
          tensor x0 N B0 D.  
         
          apply seqNtoSeq in H9;auto.
          exact U. auto.
          rewrite cxtDestruct. rewrite <- H2.
          apply in_or_app;left.
          rewrite H.
          apply uIngetU; sauto.
        ++
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- D; F::x0; (>> G)).
          seqPerm H1 H9.

          eapply HDown in H0...
          tensor M0 x0 B0 D.  
   
          apply seqNtoSeq in H5;auto.
          exact U. auto.
          rewrite cxtDestruct. rewrite <- H3.
          apply in_or_app;left.
          rewrite H.
          apply uIngetU; sauto.
      + 
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H4 ...
        exact U. auto. auto.
      +
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H4 ...
        exact U. auto. auto.
      +
        rewrite Permutation_cons_append in H5.
        eapply UpExtension in H5...
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...

        eapply HUp in H3 ...
        exact U. auto. auto.
      +
        assert(HRI: RInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H6 ...
        existential t.
        exact U. auto. auto.
    Qed.


    Theorem InvAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvCopyUP; assumption.
        apply InvCopyDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionClassic : forall i B L F  M,
        u i = true -> mt i = true -> In (i,F) B -> 
        (|-- B ; M ; UP (L++[F])) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply seqtoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros. eapply H3;eauto.
    Qed.

    Theorem AbsorptionClassic' : forall i B L F  M,
        u i = true -> mt i = true -> In (i,F) B ->
        (|-- B ; M ; UP (L++[F])) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply seqtoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros. eapply H3;eauto.
    Qed.
    
  Theorem AbsorptionClassicSet : forall B B' L C M,
        SetU C -> SetT C -> Permutation B (C++B') -> 
        |-- B ;M ; UP (L ++ second C) -> |-- B ; M ; UP L .
    Proof with sauto.
    intros.
    revert dependent L.
    revert dependent B.
    revert dependent B'.
    revert dependent M.
    induction C;intros...
    CleanContext... 
    simpl in H2.
    simpl in H1.
    destruct a as [b F].
    rewrite H1.
    eapply AbsorptionClassic' with (i:=b) (F:=F)...
    SLSolve.
    SLSolve.
    
    eapply IHC with (B':= (b, F) :: B')... SLSolve. SLSolve.
    perm.
    rewrite app_assoc_reverse.
    rewrite <- H1. exact H2.
    Qed.
    
 
  End AbsorptionClassic. 
  
 
Section AbsorptionLinear.

    Definition RLUp (n:nat) := forall i B B' L F M , 
      u i = false -> mt i = true -> Remove (i,F) B B' -> n |--- B' ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).  

    Definition RLDown (n:nat) := forall i B B' F  M  H, 
        ~ asynchronous F ->
    u i = false ->  mt i = true -> Remove (i,F) B B' -> n |--- B' ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RLInd (n:nat) := RLUp n /\ RLDown (n -1). 

    Lemma RLDown0 : RLDown 0.
    Proof with sauto;solveLL.
      unfold RLDown. intros i B B' F M H NAF ML MT FB HD.
      inversion HD...
      CleanContext.
      apply Remove_Permute in FB...
     Qed.

    Lemma RLUp0 : RLUp 0.
    Proof with subst;auto;solveLL.
      unfold RLUp. intros i B B' L F M ML MT FB HD.
      destruct L.
      + inversion HD...
        decide2l i top B'. 
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvCopyLUP: forall  n ,
        (forall m : nat, m <= n -> RLInd m) -> RLUp (S n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RLUp. intros i B B' L1 F M MU MT FB HD.
    (*   assert(HPR: Permutation B ((i,F)::B')).
      apply Remove_Permute in FB...
     *)  destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD... 
        ++
        decide2l i top B'.
        ++
           decide2l i bot B'.
          apply seqNtoSeq in H3;auto. 
        ++
        decide2l i (F0 $ G) B'.
        apply seqNtoSeq in H3;auto.
        ++ 
          decide2l i (F0 & G) B'. 
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          decide2l i (i0 ? F0) B'. 
          apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RLInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M) in H0;[|perm].
          CleanContext.
          inversion H2;subst.
          **
            decide2l i F B'. 
            apply seqNtoSeq in H1;auto.
            rewrite H3;auto.
          **    
            decide1 F0 l2. 
            eapply HDown with (F:= F) (i:=i) (B':=B') ;auto.
            
            eapply exchangeLCN with (LC:=F :: l2)...
            seqPerm H3 H1...
        *
          decide2u i0 F0.
          apply Remove_Permute in FB.
           rewrite FB. firstorder. exact nil. 
            eapply HDown with (F:= F) (i:=i) (B':=B');auto.
        *
           apply Remove_Permute in FB;auto.
           apply Remove_Permute in H2;auto.
           rewrite H2 in FB.
           rewrite FB.
           eapply exchangeCC' with (CC:=(i0, F0) :: (i, F) :: B'0).
           perm.
           decide2l i0 F0 ( (i, F) :: B'0).
           eapply HDown with (F:= F) (i:=i);auto.
        *
          decide3 F0. 
          eapply HDown with (F:= F) (i:=i) (B':=B');auto.
          ++ 
            decide2l i (F{ FX}) B'. 
            generalize (H5 x);intro.
            apply H in properX.
            apply seqNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD;subst; try(
                                 assert(RLInd n) by ( apply IH;auto);
                                 destruct H as [HLUp  HLDown]; clear HLDown) ...
        1-4: eapply HLUp with (F:=F) (i:=i) (B':=B');auto.
        eapply HLUp with (F:=F) (i:=i) (B':=(i0, F0)::B')...
        eapply HLUp with (F:=F) (i:=i) (B':=B')...       
        generalize (H5 x properX);intros...
        eapply HLUp with (F:=F) (i:=i) (B':=B')...       
        
        
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   

    Theorem InvCopyLDW: forall  n ,
        (forall m : nat, m <= n -> RLInd m) -> RLDown (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RLDown.  intros i B B' F M H FNA MU MT FB HD.
      inversion HD...
      + 
         CleanContext.
      apply Remove_Permute in FB...
      + 
        checkPermutationCases H1.
        ++ 
          assert(HRI: RLInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0; F::x ; (>> F0)).
          seqPerm H0 H5.
           
          assert(|-- (i, F) :: B0; x; (>> F0)). 
          eapply HDown ...
          tensor x N ((i, F) :: B0) D.  
          CleanContext.
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          apply seqNtoSeq in H9;auto.
        ++
          assert(HRI: RLInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- D; F::x; (>> G)).
          seqPerm H0 H9.
          assert(|-- (i, F) :: D; x; (>> G)). 
          eapply HDown ...
          tensor M0 x B0 ((i, F) :: D).  
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          apply Remove_Permute in FB...
          rewrite FB.
          CleanContext.
          rewrite <- Permutation_middle...
          apply seqNtoSeq in H5;auto.
      + 
        assert(HRI: RLInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (>> F0)). 
        eapply HDown...
        oplus1...
        apply Remove_Permute in FB...
        rewrite FB...
      +
        assert(HRI: RLInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (>> G)). 
        eapply HDown...
        oplus2...
        apply Remove_Permute in FB...
        rewrite FB...
      +
        rewrite Permutation_cons_append in H5.
        eapply UpExtension in H5...
        assert(HRI: RLInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        assert( |-- (i, F) :: B'; M; (> [H])).
        eapply HUp...
        apply Remove_Permute in FB...
        rewrite FB... 
      +
        assert(HRI: RLInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (>> FX t)).
        eapply HDown...
        existential t.
        apply Remove_Permute in FB...
        rewrite FB... 
    Qed.


    Theorem InvLAux : forall n, RLInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RLInd.
        split; [apply RLUp0 | apply RLDown0].
      + unfold RLInd in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvCopyLUP; assumption.
        apply InvCopyLDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionLinear : forall i B B' L F  M,
        mt i = true -> Remove (i,F) B B' -> 
        |-- B' ;M ; UP (L ++ [F]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      destruct (uDec i).
      apply Remove_Permute in H0;auto.
      eapply AbsorptionClassic with (i:=i) (F:=F);auto.
      rewrite H0;firstorder.
      rewrite H0.
      apply weakening;auto.
      
      assert(HRn:  forall n, RLUp n) by (apply InvLAux).
      apply seqtoSeqN in H1;auto. 
      destruct H1.
      generalize (HRn x);intros. eapply H2;eauto.
    Qed.

  Theorem AbsorptionLinearSet : forall B B' L C M,
        SetT C -> Permutation B (C++B') -> 
        |-- B' ;M ; UP (L ++ second C) -> |-- B ; M ; UP L .
    Proof with sauto.
    intros.
    revert dependent L.
    revert dependent B.
    revert dependent B'.
    revert dependent M.
    induction C;intros...
    CleanContext. rewrite H0...
    simpl in H1.
    simpl in H0.
    destruct a as [b F].
    rewrite H0.
    eapply AbsorptionLinear with (i:=b)...
    SLSolve. SLSolve.
    eapply IHC... SLSolve. SLSolve.
    rewrite app_assoc_reverse.
    exact H1.
    Qed.
    
  End AbsorptionLinear. 


  Section InvExists.


    Definition RUpExists (n:nat) := forall B L M FX t, 
      uniform_oo FX -> proper t -> 
      n |--- B ;M ; UP (L ++ [FX t])  -> |-- B ; (E{ FX}):: M; UP L.

    Definition RDownExists (n:nat) := forall B M H FX t, 
        ~ asynchronous (FX t) -> positiveFormula (FX t) -> uniform_oo FX -> proper t ->
        n |--- B ; (FX t)::M; DW H -> |-- B ;E{ FX} :: M; DW H.


    Definition RIndExists (n:nat) := RUpExists n /\ RDownExists (n -1). 

    Lemma RDownE0 : RDownExists 0.
    Proof with sauto;solveF;solveLL.
    unfold RDownExists.
     
    intros B M H FX t FNA FP Uni Ft HD.
      inversion HD...
      
      rewrite <- H0 in FP.
      inversion FP. 
    Qed.

    Lemma Remove_app_in' :
      forall (F:oo) (L: list oo), Remove F (L ++ [F]) (L).
      intros.
      assert(Remove (F) (L ++ [F]) (L++[])).
      eapply Remove_app_in with (F:=F) (L1:=L) (L2:=nil).
      rewrite app_nil_r in H.
      assumption.
    Qed.



    Lemma RUpE0 : RUpExists 0.
    Proof with subst;auto;solveF;solveLL.
      unfold RUpExists.
      intros.
      destruct L.
      + inversion H1...
        decide1 (E{ FX}) M ...
        existential t.  
          rewrite <- H6.
          release... 
      + inversion H1...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    Theorem InvExUP: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RUpExists (S n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RUpExists.  intros B L1 M1 FX t  Hu Hp HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
        decide1 (E{ FX}) M1...
        existential t.  
          rewrite <- H3.
          release...
        ++ decide1 (E{ FX}) M1...
           existential t.  
           rewrite <- H0.
           release...
           apply seqNtoSeq in H3;auto. 
        ++ decide1 (E{ FX}) M1...
           existential t.  
           rewrite <- H0.
           release...
           apply seqNtoSeq in H3;auto. 
        ++ decide1 (E{ FX}) M1...
           existential t.  
           rewrite <- H0.
           release...
           apply seqNtoSeq in H4;auto. 
           apply seqNtoSeq in H5;auto.
        ++ decide1 (E{ FX}) M1...
           existential t.  
           rewrite <- H0.
           release...
           apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RIndExists n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          eapply Remove_Permutation_Ex2 with (M:=[FX t] ++ M1) in H0;[|perm].
          CleanContext.
          inversion H2;subst.
          
          decide1 (E{ FX}) x...
          existential t.  
          rewrite H3.
          apply seqNtoSeq in H1;auto.
          
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H0...
            decide1 (E{ FX}) M1... 
            existential t.
             rewrite <- H7.
             rewrite <- H7 in H5.
           release...
           apply seqNtoSeq in H5;auto.
          }
          assert(Permutation (l2 ++ [FX t]) L') by (rewrite <- H3;perm).
          assert( n0 |--- B; (FX t)::l2; (>> F)).
          seqPerm H6 H1. perm.

          apply HDown in H7...
          decide1 F ((E{ FX})::l2) ...
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H6...
            decide1 (E{ FX}) M1... 
            existential t.
             rewrite <- H8.
             rewrite <- H8 in H5.
           release...
           apply seqNtoSeq in H5;auto. }
          eapply HDown in H3...
          decide2u i F.  
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H6...
            decide1 (E{ FX}) M1... 
            existential t.
             rewrite <- H8.
             rewrite <- H8 in H5.
           release...
           apply seqNtoSeq in H5;auto.
          }
          apply HDown in H3 ...
          decide2l i F B'.
         *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H2...
            decide1 (E{ FX}) M1... 
            existential t.
             rewrite <- H6.
             rewrite <- H6 in H5.
           release...
           apply seqNtoSeq in H5;auto.
          }
          apply HDown in H1 ...
          decide3 F.
        ++ 
            decide1 (E{ FX}) M1... 
            existential t.
            rewrite <- H0...
            generalize(H5 x properX);intro.
            apply seqNtoSeq in H;auto.
      +
        (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndExists n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        
        all: try eapply HUp with (t:=t);eauto.
        rewrite perm_swap.
          eapply HUp;eauto.
  
    Qed.


    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvExDW: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RDownExists (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDownExists.  
      intros B M H FX t HNA HP Hu Ht HD1.
      inversion HD1;subst ...
      + rewrite <- H0 in HP.
        inversion HP.
      +
        checkPermutationCases H1. 
        ++ 
          rewrite H0 in H5.
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H5 ...
          tensor (E{ FX}::x ) N B0 D.
          apply seqNtoSeq in H9;auto.
        ++ 
          rewrite H0 in H9.
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H9 ...
          tensor M0 (E{ FX}::x) B0 D.
          rewrite <- H1; perm.
          
          apply seqNtoSeq in H5;auto.
      +                   
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H4...
      +                   
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H4...
      +
        rewrite Permutation_cons_append in H5.
        eapply UpExtension in H5...
        assert(HRI: RIndExists x) by auto.
        destruct HRI as [HUp  HDown] ...

        apply HUp in H3 ...
      +
        assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H6...
          existential t0.
    Qed.

    Theorem InvExAux : forall n, RIndExists n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndExists.
        split; [apply RUpE0 | apply RDownE0].
      + unfold RIndExists in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvExUP; assumption.
        apply InvExDW; assumption.
    Qed.


    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   

    Theorem InvEx : forall B L FX t  M, 
        uniform_oo FX -> proper t -> 
        |-- B  ;M ; UP (L++[FX t ]) -> |-- B ; E{ FX}::M ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpExists n) by (apply InvExAux).
      apply seqtoSeqN in H1.
      destruct H1.
      generalize (HRn x);intros.
      apply H2 in H1;auto.
    Qed.


    Theorem InvExC : forall i B L FX t  M, u i = true -> mt i = true ->
       In (i,E{ FX}) B ->
        uniform_oo FX -> proper t -> 
        |-- B ;M ; UP (L++[FX t ]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      intro. inversion H5.
      rewrite <- Permutation_cons_append.
      apply InvEx with (t:=t);auto.
    Qed.  
    
     Theorem InvExL : forall i B B' L FX t M, u i = false -> mt i = true ->
        uniform_oo FX -> proper t -> Remove (i,E{ FX}) B B' ->
        |-- B'  ;M ; UP (L++[FX t ]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'.
      intro. inversion H5.
      rewrite <- Permutation_cons_append.
      apply InvEx with (t:=t);auto.
    Qed.
  
       Theorem InvExT : forall B L FX t M, 
        uniform_oo FX -> proper t -> theory (E{ FX}) ->
        |-- B  ;M ; UP (L++[FX t ]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      intro Hc. inversion Hc.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      apply InvEx with (t:=t);auto.
    Qed.
      
   
     
  End InvExists.

  Section InvOPlus.

    Definition RUpPlus (n:nat) := forall B L M F G, 
      n |--- B ;M ; UP (L ++ [F])  -> |-- B ; (F op G)::M; UP L.

    Definition RDownPlus (n:nat) := forall B M H F G, 
        positiveFormula F ->
        n |--- B ; F::M  ; DW H -> |-- B ; (F op G)::M; DW H.

    Definition RIndPlus (n:nat) := RUpPlus n /\ RDownPlus (n -1). 

    Lemma RDownP0 : RDownPlus 0.
    Proof with sauto;solveF;solveLL.
      unfold RDownPlus.
      intros B M H F G FP HD.
      inversion HD;subst...
      inversion FP. 
    Qed.

    Lemma RUpP0 : RUpPlus 0.
    Proof with sauto;solveF;solveLL.
      unfold RUpPlus.
      intros B L M F G HD.
      destruct L.
      + inversion HD;subst...
        decide1 (top op G) M...
        oplus1.
      + inversion HD...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvPlusUP: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RUpPlus (S n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RUpPlus.  intros B L1 M1 F G HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst ...
        ++
          decide1 (top op G). 
          oplus1.
        ++ 
          decide1 (bot op G). 
          oplus1.
          apply seqNtoSeq in H3;auto.
        ++
          decide1 ((F0 $ G0) op G). 
          oplus1.
          apply seqNtoSeq in H3;auto.
        ++ 
          decide1 ((F0 & G0) op G). 
          oplus1.
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto.
        ++
          decide1 ((i ? F0) op G). 
          oplus1.
          apply seqNtoSeq in H3;auto.
        ++ 
          assert(RIndPlus n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        *  
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M1) in H0;[|perm].
          CleanContext.
          inversion H2...
          decide1 (F op G) x...
          oplus1.
          rewrite H3.
          apply seqNtoSeq in H1;auto.

          destruct (NotAsynchronousPosAtoms H4).
          2:{
            decide1 (F op G) M1...
            oplus1.
            inversion H0...
            apply seqNtoSeq in H5;auto.
          }
          assert(n0 |--- B; (F::l2); (>> F0)).
          seqPerm H3 H1.
          decide1 F0 ((F op G)::l2)...
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            decide1 (F op G) M1...
            oplus1.
            inversion H6...
            apply seqNtoSeq in H5;auto.
          }
          eapply HDown in H3 ...
          decide2u i F0. 
          exact H3. 
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
           decide1 (F op G) M1...
            oplus1.
            inversion H6...
            apply seqNtoSeq in H5;auto.
          }
          eapply HDown in H3 ...
          decide2l i F0 B'. 
          exact H3. 
         * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
           decide1 (F op G) M1...
            oplus1.
            inversion H2...
            apply seqNtoSeq in H5;auto.
          }
          eapply HDown in H1 ...
          decide3 F0. 
          exact H1.          
          ++
            decide1 (F{ FX} op G) M1...
            oplus1.
            generalize (H5 x properX);intro.
            apply seqNtoSeq in H;auto.
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndPlus n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown)...

        all: try eapply HUp...
        rewrite perm_swap... 
    Qed.    

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvPlusDW: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RDownPlus (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDownPlus.  intros B M  H  F G HPosF HD1.
      inversion HD1;subst ...
      + 
        inversion HPosF.
      + 
    
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
       checkPermutationCases H1.
       ++
       rewrite H0 in H5.
       tensor ((F op G) ::x) N B0 D...  
       apply seqNtoSeq in H9...
       ++
       rewrite H0 in H9.
       tensor M0  ((F op G) ::x) B0 D...  
       rewrite <- H1...
       apply seqNtoSeq in H5...
     +
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
     +
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
     + 
       rewrite Permutation_cons_append in H5.
       apply UpExtension in H5...
       2:{ inversion HPosF... } 
        assert(HRI: RIndPlus x)  by auto.
        destruct HRI as [HUp  HDown] ...
      +
        assert(HRI: RIndPlus (S n0)) by auto.
        destruct HRI as [HUp  HDown] ...
        existential t.
    Qed.


    Theorem InvPlusAux : forall n, RIndPlus n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndPlus.
        split; [apply RUpP0 | apply RDownP0].
      + unfold RIndPlus in *.
        split.
        apply InvPlusUP; assumption.
        simpl;  rewrite Nat.sub_0_r.
        apply InvPlusDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem InvPlus : forall B L F G  M, 
    |-- B  ;M ; UP (L++[F]) -> |-- B ; (F op G) :: M ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpPlus n) by (apply InvPlusAux).
      apply seqtoSeqN in H.
      destruct H.
      generalize (HRn x);intros.
      eapply H0 in H;eauto.
    Qed.

   Theorem InvPlusC : forall i B L F G M, u i = true -> mt i = true ->
       In (i,F op G) B ->
        |-- B ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite Permutation_app_comm.
      apply InvPlus ;auto.
    Qed.  
    
     Theorem InvPlusL : forall i B B' L F G M, u i = false -> mt i = true ->
        Remove (i,F op G) B B' ->
        |-- B'  ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite Permutation_app_comm.
      apply InvPlus;auto.
    Qed.

     Theorem InvPlusT : forall L F G B M, 
        theory (F op G) ->
        |-- B  ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      intro Hc. inversion Hc.
      apply UpExtension'.
      
      intro Hc. inversion Hc.
      rewrite Permutation_app_comm.
      apply InvPlus ;auto.
    Qed.
    
    Lemma OPlusComm : forall B M F G X n,
     n |--- B ; M ++ [F op G] ; X -> n |--- B ; M ++ [G op F] ; X.
    Proof with sauto;solveF;solveLL.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
      + 
        inversion H0...
        ++ 
          eapply Remove_Permutation_Ex2 with (F:=F op G) (L':= M) in H2.
          2:{ apply Remove_app_in'. }
          CleanContext.

          apply Remove_Permute in H2;auto.
          apply PProp_perm_select' in H2.
          CleanContext.

          assert(Permutation (F op G :: x0) (x0 ++ [F op G])).
          perm.
          rewrite H1 in H2. rewrite H2 in H6.
          eapply H in H6...
          tensor (x0 ++ [G op F]) N B0 D...
          rewrite <- H8. rewrite <- H9. perm.
        
          assert(Permutation (F op G :: x0) (x0 ++ [F op G])).
          perm.
          rewrite H1 in H2. rewrite H2 in H7.
          eapply H in H7...
          tensor M0 (x0 ++ [G op F]) B0 D...
          rewrite <- H8. rewrite <- H9. perm.
        ++
          assert (n |--- B; (M ++ [F0]) ++ [F op G]; (> M0)).
          LLExact H3.
          eapply H in H1...
          LLExact H1.
        ++ 
          eapply Remove_Permutation_Ex2 with (M:=[F op G] ++ M) in H3;[|perm].
          CleanContext.
          inversion H3...
      
          decide1 (G op F) x...

          apply Remove_app_in'.
          rewrite H5. 
          inversion H4...

          decide1 F0  (l2++[G op F])...
          assert(Permutation (F op G :: l2) (l2++[F op G])).
          perm.
          rewrite H1 in H5.
          rewrite <- H5 in H4.
          apply H in H4...
       ++
       decide2u i F0.
       ++
       decide2l i F0 B'.
          
        ++
       decide3 F0.
        ++ 
          existential t. 
       
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM (FLIPPING F and G)   *)
    (* =============================================== *)   
    Theorem InvPlusComm: forall B L F G  M, 
     |-- B  ;M ; UP (L++[G]) -> |-- B ; (F op G)::M ; UP L .
    Proof.
      intros.
      apply InvPlus with (G:=F)in H;auto.
      apply seqtoSeqN in H.
      destruct H.
      rewrite Permutation_cons_append in H.
      apply OPlusComm in H.
      apply seqNtoSeq with (n:=x) in H;auto.
      LLExact H.
    Qed.

    Theorem InvPlusCComm : forall i B L F G M, u i = true -> mt i = true ->
       In (i,F op G) B ->
        |-- B ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      apply InvPlusComm ;auto.
    Qed.  
    
     Theorem InvPlusLComm : forall i B B' L F G M, u i = false -> mt i = true ->
        Remove (i,F op G) B B' ->
        |-- B'  ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      apply InvPlusComm;auto.
    Qed.
    
    Theorem InvPlusTComm : forall L F G B M, 
        theory (F op G) ->
        |-- B  ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      intro Hc. inversion Hc.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      apply InvPlusComm ;auto.
    Qed.
    
    
  End InvOPlus.

  (* =============================================== *)
  (** Invertibility of Tensor *)
  (* =============================================== *)   
  Section InvTensor.

    Definition RUpTensor (nm:nat) := forall BD B D L M L' M' F G n m, 
      nm = n + m ->  (* isFormulaL L -> *)
      Permutation (getU BD) (getU B) ->
      Permutation (getU BD) (getU D) ->
      Permutation (getL BD) (getL B ++ getL D) ->
      n |--- B ;M ; UP (L ++ [F]) -> 
      m |--- D ;M' ; UP (L' ++ [G])  -> 
        |-- BD ; (F ** G) :: M ++ M'; UP (L ++ L').

    Definition RDownTensor (nm:nat) := forall BD B D M M' H F G n m, 
        nm = n + m -> positiveFormula F -> 
        Permutation (getU BD) (getU B) ->
        Permutation (getU BD) (getU D) ->
        Permutation (getL BD) (getL B ++ getL D) ->
        n |--- B ; F::M; DW H -> 
        m |--- D ; M' ; UP [G] -> 
          |-- BD ; (F ** G) :: M ++ M'  ; DW H.

    Definition RIndTensor (n:nat) := RUpTensor n /\ RDownTensor (n -1). 

    Lemma RDownT0 : RDownTensor 0.
    Proof with sauto;solveF;solveLL.
      unfold RDownTensor. 
      intros *. intros MN FP P1 P2 P3 HD1 HD2.
    
      symmetry in MN. 
      apply plus_is_O in MN.
      destruct MN...

      inversion HD1...
      inversion FP.
     
     Qed.

    Lemma RUpT0 : RUpTensor 0.
    Proof with sauto;solveF;solveLL.
      unfold RUpTensor. 
      intros *.
      intros MN  P1 P2 P3 HD1 HD2.
      symmetry in MN. apply plus_is_O in MN.
      destruct MN...
      inversion HD1...
      destruct L;destruct L';simpl in *.
      +
        inversion HD1...
        inversion HD2...
        decide1 (top ** top) (M++M')... 
        tensor M M' B D. 
      + 
        inversion H3... inversion HD2...
      + 
        inversion H3 ...
      + 
        inversion H3 ...
    Qed.
    (* =============================================== *)
    (* F ** G COMMUTES *)
    (* =============================================== *)
    Lemma TensorComm : forall B M F G X n, n |--- B ; M ++ [F ** G] ; X -> n |--- B ; M ++ [G ** F] ; X.
    Proof with sauto;solveF;solveLL.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
      + 
        inversion H0...
        ++ 
          apply PProp_perm_sel in H2.
          CleanContext.
        *
          rewrite H2 in H6.
          apply H in H6...
          tensor (x ++ [G ** F]) N B0 D.
         rewrite <- H8... 
        *
          rewrite H2 in H7.
          apply H in H7...
          tensor M0 (x ++ [G ** F]) B0 D.
         rewrite <- H8... 
          ++ 
            assert(n |--- B; (M ++ [F0]) ++ [F ** G]; (> M0)).
            LLExact H3.
            apply H in H1...
            LLExact H1.
          ++ 
            eapply Remove_Permutation_Ex2 with (M:=[F ** G] ++ M) in H3;[|perm].     CleanContext.
       
            inversion H3...
            2:{ 
            
            decide1 F0 (l2 ++ [G ** F]).
              apply Remove_app_tail;auto.
              apply H...
              LLExact H4.
              rewrite <- H5...  }
              inversion H4...
            decide1 (G**F) x.
            apply Remove_app_in'.
            tensor N M D B0.
            rewrite H5... rewrite H6...
            rewrite Permutation_app_comm... 
          ++  
            decide2u i F0 ...
          ++  
            decide2l i F0 B' ...
         
          ++  
            decide3 F0 ...
         
          ++ 
            existential t. 
           
    Qed.


    Lemma TensorComm' : forall B M F G X , |-- B ; M ++ [F ** G] ; X -> |-- B ; M ++ [G ** F] ; X.
    Proof.
      intros.
      apply seqtoSeqN in H.
      destruct H.
      apply TensorComm in H.
      eapply seqNtoSeq in H;eauto.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Cases when one of the lists is not empty *)
    (* =============================================== *)
    Lemma InvTensorConsNil (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) BD B D (L1 M1 : list oo)
     (l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
       isFormulaL L1 -> 
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->
       n' |--- B; M1; UP (L1 ++ [F]) -> 
       m' |--- D; M2; UP (l :: L2 ++ [G]) -> 
          |-- BD; (F ** G) :: M1 ++ M2; UP (L1 ++ l :: L2).
    Proof with sauto;solveF;solveLL.
      intros. 
      inversion H5...
      + apply EquivAuxTop...
      + apply EquivAuxBot...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with (n0:=n') (m:=n) (B:=B) (D:=D)...
      + apply EquivAuxPar...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D)...
      + apply EquivAuxWith...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D)...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D)...
      + destruct (uDec i).
        apply EquivAuxQuest...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n0:=n') (m:=n) (B:=B++[(i, F0)]) (D:=D++[(i, F0)])... 
        simplSignature. rewrite H1...
        simplSignature. rewrite H2...
        simplSignature. rewrite H3...
        eapply weakeningGenN_rev;auto.
        LLExact H10.
        apply EquivAuxQuest...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D++[(i, F0)])...
          simplSignature. rewrite H1...
        simplSignature. rewrite H2...
        simplSignature. rewrite H3...
        LLExact H10.
      +
        apply EquivAuxStore...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        rewrite <- app_assoc.
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D)...
        LLExact H12.
      +
        apply EquivAuxForAll;intros...
        generalize (H12 t H6);intro.
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia).
        eapply HUp with(n0:=n') (m:=n) (B:=B) (D:=D)...
    Qed.

Lemma InvTensorConsNil' (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) BD B D (L1 M1 : list oo)
     (l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
       L1 <> [] -> 
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->
       n' |--- B; M1; UP (L1 ++ [F]) -> 
       m' |--- D; M2; UP (l :: L2 ++ [G]) -> 
          |-- BD; (F ** G) :: M1 ++ M2; UP (L1 ++ l :: L2).
    Proof with sauto;solveF;solveLL.
      intros. 
      inversion H4...
      + apply ListConsApp in H10... 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)... 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        
        repeat rewrite app_comm_cons.
        rewrite <- app_comm_cons.
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)... 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        repeat rewrite app_comm_cons.
        rewrite <- app_comm_cons.
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)... 
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        repeat rewrite app_comm_cons.
        rewrite <- app_comm_cons.
        
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)... 
      + apply ListConsApp in H6...
        destruct (uDec i).
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        eapply HUp with (n0:=n) (m:=m') (B:=B++[(i, F0)]) (D:=D++[(i, F0)])... 
        CleanContext.
        rewrite H1...  
        CleanContext.
        rewrite H2...
        CleanContext.
         LLExact H10.  
        eapply weakeningGenN_rev;auto.
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        eapply HUp with (n0:=n) (m:=m') (B:=B++[(i, F0)]) (D:=D)... 
        CleanContext.
        CleanContext.
        rewrite e...
        CleanContext.
        rewrite H3...
        LLExact H10.  
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        do 2 rewrite app_comm_cons.
        rewrite Permutation_cons_append.
        repeat rewrite <- app_comm_cons.
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)...
        LLExact H11. 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        repeat rewrite app_comm_cons.
        rewrite <- app_comm_cons.
        eapply HUp with (n0:=n) (m:=m') (B:=B) (D:=D)... 
    Qed.


    (* ================================================ *)
    (* PROOF OF RUP *)
    (* Case when the 2 formulas are async. or pos. atoms*)
    (* ================================================ *)

    Lemma ITCaseAsyncAsync:
      forall n m BD B D M1 M2 F G, 
      (asynchronous F \/  IsPositiveAtom F) -> 
      (asynchronous G \/ IsPositiveAtom G) -> 
        Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->
       (n |--- B; M1; UP [F]) -> 
       (m |--- D; M2; UP [G]) -> 
       |-- BD; (F ** G):: M1 ++ M2; UP [].
    Proof.
      intros.
      decide1 (F ** G). 
      tensor M1 M2 B D...
      release. 
      apply AsIsPosRelease;auto.
      apply seqNtoSeq in H4;auto.

      release.
      apply AsIsPosRelease;auto.
      apply seqNtoSeq in H5;auto.
   Qed.

    (** We assume that the theory produces only well-formed LL formulas *)
    Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.

    Lemma ITAsyncSync  :
      forall nm n m BD B D M1 M2 F G,
        (asynchronous F \/ IsPositiveAtom F) ->  ~ asynchronous G ->         
        (forall m : nat, m <= nm -> RIndTensor m) -> nm = n + m -> 
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->
        n |--- B; M1; UP [F] ->  
        m |--- D; M2 ++ [G]; UP [] ->  
          |-- BD; (F ** G) :: M1 ++ M2; UP [].
    Proof with subst;auto;auto;solveF;solveLL.
      intros. 
      apply NotAsynchronousPosAtoms' in H0; destruct H0 as [AG | AG].
      +
        (* G is a positive atom... then, release works (Lemma  ITCaseAsyncAsync) *)
        eapply ITCaseAsyncAsync with (n:=n) (m:=S m) (B:=B) (D:=D);eauto. 
        apply tri_store;auto using IsPositiveAtomNotAssync...
        LLExact H7. 
      +
        (* G cannot do release *)
       
        inversion H7...
        ++ eapply Remove_Permutation_Ex2 with (M:=G::M2) in H8...  
           CleanContext.
           inversion H8...
        * decide1 (F ** G). 
          tensor M1 x B D.
          release. apply AsyncRelease;auto.
          apply seqNtoSeq in H6;auto. 
          rewrite H10.
          apply seqNtoSeq in H9;auto. 
        * 
          decide1 F0 ((F ** G) ::M1 ++ l2)...
          constructor.
          eapply Remove_app_head;auto.
          
          assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto); destruct IH2 as [HUp HDw].
          assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
          rewrite Permutation_cons_append.   
          apply TensorComm'.
          rewrite (Permutation_app_comm M1).
           rewrite <- Permutation_cons_append. 
           eapply HDw with (m:= n) (n1:= n0) (B:=D) (D:=B);try(lia)...
           rewrite H5...
          rewrite <- H10 in H9.
          LLExact H9.
       *  
          inversion H8...
          decide1 (F ** G). 
          tensor M1 x B D.
          release. apply AsIsPosRelease;auto.
          apply seqNtoSeq in H6;auto. 
          rewrite H10.
          apply seqNtoSeq in H9;auto.
           decide1 F0 ((F ** G) ::M1 ++ l2)...
          constructor.
          eapply Remove_app_head;auto.
          
          assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto); destruct IH2 as [HUp HDw].
          assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
             rewrite Permutation_cons_append.   
          apply TensorComm'.
          rewrite (Permutation_app_comm M1).
          rewrite <- Permutation_cons_append.   
           eapply HDw with (m:= n) (n1:= n0) (B:=D) (D:=B);try(lia)...
           rewrite H5...
          rewrite <- H10 in H9.
          LLExact H9. 
  
     ++ assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
         destruct IH2 as [HUp HDw].
         assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
          rewrite cxtDestruct.
          rewrite H5.
          decide2u i F0.
          apply in_or_app. left. 
          rewrite H4.
          apply uIngetU...
          rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1).   
            eapply HDw with (m:= n) (n1:= n0) (B:=D) (D:=B);try(lia)...
            simplSignature.
            rewrite H4...
             simplSignature.
            rewrite H3...
        LLExact H11. 
      ++ assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
         destruct IH2 as [HUp HDw].
         assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
             rewrite cxtDestruct.
            rewrite H5.
             apply Remove_Permute in H10.
             rewrite H10.
             simplSignature.
            decide2l i F0 (getU BD ++ getL B ++ getL B')...
             do 2 rewrite app_assoc.
             apply Remove_app_in.
             rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1).   
            eapply HDw with (m:= n) (n1:= n0) (B:=B') (D:=B);try(lia)...
            simplSignature. 
            rewrite H4... rewrite H10.
            simplSignature... 
            simplSignature.
            rewrite H3... 
            LLExact H11.
           firstorder.
          ++ 
            assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
              destruct IH2 as [HUp HDw].
            assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
            decide3 F0 ...
             rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1).  
            eapply HDw with (m:= n) (n1:= n0) (B:=D) (D:=B);try(lia)...
            rewrite H5...
            LLExact H9.
        ++ sauto.    
Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Case when both formulas are not Async *)
    (* =============================================== *)
    Lemma ITSyncSync : forall nm n m  BD B D M1 M2 F G, 
    ~ asynchronous F -> ~ asynchronous G ->  
    (forall m : nat, m <= nm -> RIndTensor m) -> S nm = S n + S m -> 
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->     
              S n |--- B; M1 ; UP [F] -> 
              S m |--- D; M2 ; UP [G] ->  
              |-- BD; (F ** G)::M1 ++ M2; UP [].
    Proof with subst;auto;solveF;solveLL.
      intros * . 
      intros AF AG IH Hnm P1 P2 P3 HD1 HD2. 
      apply NotAsynchronousPosAtoms' in AF; destruct AF as [AF | AF];
        apply NotAsynchronousPosAtoms' in AG; destruct AG as [AG | AG].
      + (* Both are positive *)
        eapply ITCaseAsyncAsync with (B:=B) (D:=D);eauto.
      + (* F is a positive atom *)
        assert(~asynchronous G).
        intro.
        inversion H;subst;inversion AG...
        assert(~asynchronous F) by auto using IsPositiveAtomNotAssync.
        inversion HD2...
        eapply ITAsyncSync with (nm:=nm) (n:= S n) (m:= m) (B:=B) (D:=D)... lia.
        LLExact H7.
      + (* G is a positive atom *)
        assert(~asynchronous G) by auto using IsPositiveAtomNotAssync.
        assert(~asynchronous F).
        intro.
        inversion H0;subst;inversion AF...
        inversion HD1...
        rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1).  
            eapply ITAsyncSync with (nm:=nm) (n:= S m) (m:= n) (B:=D) (D:=B);try lia...
            rewrite P3...
            LLExact H7. 
       +  (* F nor G can do release *)
        assert(~asynchronous G).
        intro.
        inversion H;subst;inversion AG...
        assert(~asynchronous F).
        intro.
        inversion H0;subst;inversion AF...
        inversion HD1...
        inversion HD2...
          
        inversion H7;subst...
        2:{
        
        decide2u i F0. rewrite cxtDestruct. rewrite P1.
        apply in_or_app. left. 
          apply uIngetU...
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n:= n0) (m0:= S m) (B:=B) (D:=D);try lia...
        }
       3:{ 
        decide3 F0. 
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n:= n0) (m0:= S m) (B:=B) (D:=D);try lia...
          }

        ++ (* DEC1 DEC1 *)
        eapply Remove_Permutation_Ex2 with (M:=F::M1) in H2...  
        CleanContext.
         inversion H4...
       2:{   decide1 F0 ((F ** G) :: l2++M2).
           constructor.
           apply Remove_app_tail;auto.
      
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
       
          eapply HDw with (n:= n0) (m0:= S m) (B:=B) (D:=D);try lia... 
          rewrite <- H5 in H3.
          LLExact H3. }
          clear H4.
rewrite H5 in *. clear H5. inversion H9...
          -
           eapply Remove_Permutation_Ex2 with (M:=G::M2) in H0...  
        CleanContext.
        inversion H4...
        2:{ decide1 F0 ((F ** G)::L'++l2).
           constructor.
           apply Remove_app_head;auto.
       
   assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm L').  
                 eapply HDw with (n1:= n) (m:= S (S n0)) (B:=D) (D:=B);try lia... 
                 rewrite P3...
                 rewrite <- H5 in H2.
                 LLExact H2. }
 
          decide1 (F**G).  
          tensor L' x0 B D.
          apply seqNtoSeq in H3...
          rewrite H5.
          apply seqNtoSeq in H2...
          -
           decide2u i F0. 
           rewrite cxtDestruct.
           rewrite P2.
            apply in_or_app. left. 
          apply uIngetU...
          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm L').  
            
          eapply  HDw with (n1:= n) (m:= S (S n0)) (B:=D) (D:=B);try lia...
          rewrite P3...
          -
            rewrite cxtDestruct.
            rewrite P3.
             apply Remove_Permute in H4.
             rewrite H4.
             CleanContext. 
             decide2l i F0 (getU BD ++ getL B ++ getL B')...
             do 2 rewrite app_assoc.
             apply Remove_app_in.

          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm L').  
          eapply  HDw with (n1:= n) (m:= S (S n0)) (B:=B') (D:=B);try lia...
          rewrite P2. rewrite H4.
          simplSignature...
          rewrite P1. 
          simplSignature...
          
    
          firstorder.
         -
         decide3 F0. 
          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
         rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm L').  
          eapply  HDw with (n1:= n) (m:= S (S n0)) (B:=D) (D:=B);try lia...
     rewrite P3...
    ++ 
       rewrite cxtDestruct.
       rewrite P3.
       apply Remove_Permute in H4.
       rewrite H4.
       simplSignature.
             
       decide2l i F0 (getU BD ++ getL B' ++ getL D)...
       apply Remove_app_in.

       assert (IH' : RIndTensor (S m + S n0)) by ( apply IH; lia).
       destruct IH' as [HUp  HDw].
       assert(Hn : S m + S n0 - 1 = m + S n0) by lia;rewrite Hn in HDw;clear Hn.
            
       eapply  HDw with (n:= n0) (m0:=S m) (B:=B') (D:=D);try lia... 
       rewrite P1. rewrite H4. 
       simplSignature...
       rewrite P2. 
       simplSignature...
       firstorder.
       Qed.
     (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)
    Theorem InvTensorUP: forall  nm , 
    (forall m : nat, m <= nm-> RIndTensor m) -> RUpTensor (S nm).
    Proof with sauto;solveF;solveLL.
      intros nm IH.
      unfold RUpTensor.
      intros BD B D L1  M1 L2 M2 F  G n' m' HNM  P1 P2 P3 HD1 HD2.
      destruct L1;destruct L2;simpl in *.
      + (* L1 and L2 are Empty *)   
        inversion HD1;inversion HD2;subst;
         
          try(
              match goal with
              | [ P3: Permutation (getL ?BD) (getL ?B ++ getL ?D)|- |-- ?BD; (?F ** ?G)::?M1 ++ ?M2; UP [] ]
                => tryif (assert(HAFG : asynchronous F /\ asynchronous G) by (split;constructor;auto))
                then
                  eapply ITCaseAsyncAsync with (B:=B) (D:=D);eauto
                else idtac
              end)... 
 
      
        eapply ITAsyncSync with  (nm := nm) (n:= n') (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor. LLExact H10. 

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor. LLExact H11.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor. LLExact H11.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor. LLExact H12.
        
        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor.  LLExact H11.

        rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1).  

        eapply ITAsyncSync with  (nm := nm) (n:= m') (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.
        
        rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 

        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.
        
         rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.
        rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.
        rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.

   
        (* both F and G are not asynchronous formulas *)
        eapply  ITSyncSync with (nm := nm) (n:=n) (m:=n0) (B:=B) (D:=D)...

 rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=D) (D:=B);try lia...
        left;constructor.
        rewrite P3... LLExact H5.

        eapply ITAsyncSync with  (nm := nm) (n:=S n) (m:=n0) (B:=B) (D:=D);try lia...
        left;constructor.
        LLExact H12.
      + (* L1 is empty and L2 is not empty *)
        eapply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (B:=B) (D:=D) (L1 := [])...
        
       + (* L1 is not empty and L2 is empty *)
        sauto. 
         rewrite Permutation_cons_append.   
            apply TensorComm'.
            rewrite <- Permutation_cons_append.
            rewrite (Permutation_app_comm M1). 
        rewrite <- (app_nil_l (o::L1)).
        eapply InvTensorConsNil with (nm:=nm) (n':=m') (m':=n') (B:=D) (D:=B);try lia...
        rewrite P3...
      +  (* L1 and L2 are not empty *)
        apply InvTensorConsNil' with (nm:=nm) (n':=n') (m':=m') (L1 := o :: L1) (B:=B) (D:=D)...
        discriminate.
   Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)
    Theorem InvTensorDW: forall  n , (forall m : nat, m <= n -> RIndTensor m) -> RDownTensor (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDownTensor.
      intros *. intros Hnm HPosF P1 P2 P3 HD1 HD2.
      inversion HD1...
      + inversion HPosF .
      +
      checkPermutationCases H1.
        ++ 
          assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
           CleanContext.
           rewrite cxtDestruct.
           rewrite P3.
           rewrite H4.
          tensor (F ** G::x ++ M') N (getU BD++(getL B0++getL D)) (getU BD++getL D0)...
          rewrite <- H1. perm.
          eapply HDown with (m0:=m) (n:=n1) (B:=B0) (D:=D) ;try lia...
          simplSignature.
          rewrite P1;auto.
          rewrite H2...
          simplSignature.
          rewrite P2...
          simplSignature... 
          rewrite <- H0;auto.
          apply seqNtoSeq in H9;auto.
          rewrite P1.
          rewrite H3.
          rewrite <- cxtDestruct;auto.
          
        ++ 
          assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 

          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.
           rewrite cxtDestruct.
           rewrite P3.
           rewrite H4.
          tensor M0 (F ** G::x ++ M' ) (getU BD++getL B0) (getU BD++(getL D0++getL D)). 
          rewrite <- H1. perm.
           apply seqNtoSeq in H5.
          rewrite P1.
          rewrite H2.
          rewrite <- cxtDestruct;auto.
        
          eapply HDown with (m0:=m) (n:=n1) (B:=D0) (D:=D) ;try lia...
          simplSignature.
          rewrite P1...
          simplSignature...
          simplSignature... 
          rewrite <- H0;auto.
      +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        oplus1. 
        eapply HDown  with (n:=n1) (m0:=m)  (B:=B) (D:=D) ... lia. 
      +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        oplus2. 
        eapply HDown  with (n:=n1) (m0:=m)  (B:=B) (D:=D)... lia. 
      +
 assert(~ asynchronous F). intro Hc.
        inversion HPosF;subst;inversion Hc...
        rewrite Permutation_cons_append in H5.
        apply UpExtension in H5 ...
        assert(HRI: RIndTensor (m + x)). apply IH. lia.
        destruct HRI as [HUp  HDown]. clear HDown.
        rewrite <- (app_nil_r [H]). 
        eapply HUp with (n:= x )(m0:= m) (B:=B) (D:=D)...
        lia.
      +   
        assert(HRI: RIndTensor (m + S n1 )) by ( apply IH;lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : m + S n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        existential t. 
                eapply HDown with (n:=n1) (m0:=m) (B:=B) (D:=D)...  
        lia.
    Qed.

    Theorem InvTensorAux : forall n, RIndTensor n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTensor.
        split; [apply RUpT0 | apply RDownT0].
      + unfold RIndTensor in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvTensorUP; assumption.
        apply InvTensorDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)

    Theorem InvTensor : forall BD B D L L' F G  M M',
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) ->  
        |-- B ; M ; UP (L++[F]) -> 
        |-- D ; M'; UP (L'++[G]) -> 
        |-- BD ; F ** G :: M ++ M' ; UP (L ++ L') .
    Proof with sauto;solveF;solveLL.
      intros.
      assert(HRn:  forall n, RUpTensor n) by (apply InvTensorAux).
      apply seqtoSeqN in H2.
      apply seqtoSeqN in H3.
      destruct H2.
      destruct H3.
      generalize (HRn (x + x0));intros.
      eapply H4 with (B:=B) (D:=D)...
    Qed.

    Theorem InvTensorC : forall i BD B D L L' F G M M', u i = true -> mt i = true ->
       In (i,F ** G) BD ->
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) -> 
        |-- B ; M ; UP (L++[F]) -> 
        |-- D ; M'; UP (L'++[G]) -> 
        |-- BD ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      eapply InvTensor with (B:=B) (D:=D) (BD:=BD) ;auto.
    Qed.  
    
     Theorem InvTensorL1 : forall i BD B B' D L L' F G M M', u i = false -> mt i = true ->
        Remove (i,F ** G) B B' ->
        Permutation (getU BD) (getU B) ->
        Permutation (getU BD) (getU D) ->
        Permutation (getL BD) (getL B ++ getL D) -> 
         |-- B' ; M ; UP (L++[F]) -> 
         |-- D ; M'; UP (L'++[G]) -> 
         |-- BD ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      rewrite cxtDestruct.
      rewrite H2.
      rewrite H4.
      apply Remove_Permute in H1;auto.
      rewrite H1 in *.
      CleanContext.
      LLPerm((i, F ** G) :: getU B' ++ getL B' ++ getL D).
      
      eapply @AbsorptionLinear with (F:=F**G) (B':=getU B'++getL B'++getL D);eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      eapply InvTensor with (B:=B') (D:=D);auto.
      CleanContext.
      CleanContext.
      rewrite <- H2.
      CleanContext.
    Qed.
  
    Theorem InvTensorL2 : forall i BD B D D' L L' F G M M', u i = false -> mt i = true ->
        Remove (i,F ** G) D D' ->
        Permutation (getU BD) (getU B) ->
        Permutation (getU BD) (getU D) ->
        Permutation (getL BD) (getL B ++ getL D) -> 
         |-- B ; M ; UP (L++[F]) -> 
         |-- D' ; M'; UP (L'++[G]) -> 
         |-- BD ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      rewrite cxtDestruct.
      rewrite H3.
      rewrite H4.
      apply Remove_Permute in H1;auto.
      rewrite H1 in *.
      CleanContext.
      LLPerm((i, F ** G) :: getU D' ++ getL D' ++ getL B).
      
      eapply @AbsorptionLinear with (F:=F**G) (B':=getU D'++getL D'++getL B);eauto.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      eapply InvTensor with (B:=B) (D:=D');CleanContext.
    Qed.
    
    Theorem InvTensorT : forall BD B D L L' F G M M', 
       theory (F ** G) ->
       Permutation (getU BD) (getU B) ->
       Permutation (getU BD) (getU D) ->
       Permutation (getL BD) (getL B ++ getL D) -> 
        |-- B ; M ; UP (L++[F]) -> 
        |-- D ; M'; UP (L'++[G]) -> 
        |-- BD ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      intro Hc. inversion Hc.
      apply UpExtension'.
      intro Hc. inversion Hc.
      rewrite <- Permutation_cons_append.
      eapply InvTensor with (B:=B) (D:=D) (BD:=BD) ;auto.
    Qed.  
      
  End InvTensor.
End InvPosPhase.
