(** * Invertibility results for the negative phase

This file proves that exchange is admissible also in the list L in
[seq Gamma Delta (> L)]. For that, some invertibility lemmas are
needed.
 *)
Require Export MMLL.Misc.Hybrid.
Require Export MMLL.SL.FLLTactics.
Require Import Lia.
Require Import MMLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section InvNPhase .
    Context `{SI : Signature}.
  Context `{OLS: OLSig}.
  Hint Constructors isFormula  Remove seqN IsPositiveAtom : core .

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).

  Theorem exp_weight0LF : forall l L, 0%nat = complexity l + complexityL L -> False.
  Proof.
    intros.
    assert(complexity l > 0%nat) by (apply Complexity0).
    lia.
  Qed.

  
  Theorem EquivAuxBot :  forall CC LC M M',
      (|-- CC ; LC ; (> M ++ M') ) ->
      (|-- CC ;  LC ; (> M ++ Bot :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    destruct a; simpl in *; invTri' H0;solveLL; 
      repeat rewrite app_comm_cons.
    all:  try match goal with
          |  [ |- seq _ _ _ (> ?M ++ bot :: _) ] =>
             eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
          end. 
    assert (Hvar : proper (VAR con 0)) by constructor.
    generalize (ComplexityUniformEq H5 properX Hvar);intro.
    lia.
  Qed.

  Theorem EquivAuxWith :  forall F G CC LC M M',
      (|-- CC ; LC ; (> M ++ [F] ++ M') ) ->
      (|-- CC ; LC ;(> M ++ [G] ++ M') ) ->
      (|-- CC ; LC ; (> M ++ (AAnd F G) :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons.
   all:   try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ (AAnd _ _) :: _) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto
            end] .
    eapply H with (M:= o x:: M) (m:= complexityL (o x:: M));simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto.
    generalize (ComplexityUniformEq H6 properX (proper_VAR con 0));intro...
  Qed.
  
  
  
  Theorem EquivAuxPar : forall F G CC LC M M',
      (|-- CC ; LC ; (> M ++ [F ; G] ++ M') ) ->
      (|-- CC ; LC ;(> M ++ (MOr F G) :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
      match goal with
      |  [ |- seq _ _ _ (> ?M ++ (MOr F G) :: _) ] =>
         eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
      end.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0));intro...
  Qed.
  
  Theorem EquivAuxStore :
    forall F CC LC M M', ~ asynchronous  F ->
                         (|-- CC ; (LC ++ [F]) ;(> M ++ M') ) ->
                         (|-- CC ; LC ; (> M ++ F :: M') ) .
  Proof with sauto.
  
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC;
    revert dependent LC;
    revert dependent M;
    revert dependent M'.
    induction SizeM using strongind;intros ...
    - symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
      store.
      LLExact H0.
    - destruct M as [ | a]; simpl in HeqSizeM.
      inversion HeqSizeM.
      destruct a;CleanContext;invTri' H1;try rewrite <- app_comm_cons;solveLL.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a1 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a2 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.                  
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.                  
      -- rewrite app_comm_cons.
         rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a1 :: a2 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.        
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.              
      -- rewrite app_comm_cons.
         eapply H0 with (m:= complexityL (o x :: M))...
         inversion HeqSizeM;simpl;try lia.       
         generalize (ComplexityUniformEq H6 properX (proper_VAR con 0));intro...  rewrite <- app_comm_cons...
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia. 
  Qed.
  
  
  Theorem EquivAuxQuest : forall a F CC LC M M',
      (|-- (CC ++ [(a,F)]) ; LC ;(> M ++  M') ) ->
      (|-- CC ; LC ; (> M ++ [a ? F] ++ M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    simpl;solveLL...
    LLExact H.
  
    destruct M; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct o; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ (Quest _ _) :: _) ] =>
              eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto
            end] .
    
    eapply H with (m:= complexityL (o x :: M));simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0));intro...
  Qed.
  
  
  Theorem EquivAuxTop :  forall CC LC M M',
      isFormulaL M ->
      (|-- CC ; LC ; (> M ++ Top :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    
    solveLL ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *;solveLL;
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ top :: _) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF; inversion H0;subst;auto
            end].
    
    eapply H with (m:= complexityL (a1 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a1 :: a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...

    inversion H0... inversion H3...
    rewrite <- app_comm_cons. solveLL...
    eapply H with (M:= o x :: M) (m:= complexityL (o x ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.

    
    rewrite (ComplexityUniformEq  H2 properX (proper_VAR con 0));auto.
  Qed.

  Theorem EquivAuxForAll : forall FX CC LC M M' ,
      isFormulaL M -> uniform_oo FX ->
      (forall t, proper t ->  (|-- CC ; LC ; (> M ++ (FX t) ::M') )) ->
      (|--  CC ; LC ; (> M ++ F{ FX} :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL.
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    inversion H1...
    
    destruct a; simpl in *;solveLL;
      try solve [eapply H with (m:= complexityL M);inversion HeqSizeM;subst;solveF;intros;solveLL; inversion H1;subst;auto;
                 generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF]...

    
    eapply H with (M:= a1 :: M)(m:= complexityL (a1 :: M));inversion HeqSizeM;subst... simpl. lia.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a2 :: M)(m:= complexityL (a2 :: M));inversion HeqSizeM;subst;solveF.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a1 :: a2 :: M)(m:= complexityL (a1 :: a2 :: M));inversion HeqSizeM;subst;solveF.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.
   inversion H5...
    solveLL.
    eapply H with (M:=  o x :: M)(m:= complexityL (o x :: M));inversion HeqSizeM;subst;solveF.
    generalize (ComplexityUniformEq H4 properX (proper_VAR con 0));intros...
    intros...
    generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.
  Qed.
  

  Theorem EquivUpArrow : forall B L L' M n,
      isFormulaL L' ->
      (n |--- B ; M ; UP L) ->
      Permutation L L' ->
      |-- B ; M ;  UP L'.
  Proof with sauto.
    intros.
    remember (complexityL L) as w.
    generalize dependent n .
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l]...
    +  apply seqNtoSeq in H0;auto.
    + inversion Heqw.
      apply exp_weight0LF in H3...
    +  destruct L' as [| l']...
       
       assert
         ((l = l' /\ Permutation L L') \/
          (exists L1 L2 L1' L2', L = L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2' /\ Permutation (L1 ++ L2) (L1' ++ L2') )) .
       { checkPermutationCases H1.
         right.
         assert (exists T1 T2, L' = T1 ++ [l] ++ T2).
         { induction x.
           do 2 eexists []...
           sauto.
           assert (In l  L') as Hm.
           rewrite H2...
           apply in_split;auto. } 
         assert (exists T1 T2, L = T1 ++ [l'] ++ T2).
         { induction x.
           do 2 eexists []...
           sauto.
           assert (In l'  L) as Hm.
           rewrite H3...
           apply in_split;auto. }
          simplifier.
       eexists x0; eexists x1;eexists x2; eexists x3. 
       intuition. 
      rewrite H4 in H3.
      simpl in H3.
      rewrite Permutation_midle in H3. 
      apply Permutation_cons_inv in H3.
      rewrite H1 in H2.
      simpl in H2.
      rewrite Permutation_midle in H2. 
      apply Permutation_cons_inv in H2.
      rewrite H2. rewrite H3. auto. }
      destruct H2 as [Heq | Heq].
        ++ destruct Heq;subst.
           inversion H0;subst;try(simpl in Heqw; inversion Heqw; subst;simpl;try(lia)).
           +++  (* top *)
             eapply tri_top'.
           +++ (* bottom *)
             eapply IH with (L' :=L') in H7;auto.
             inversion H;subst;auto.
           +++ (* par *)
             eapply IH with (L' := F::G::L') in H7;auto.
             inversion H;subst.
             inversion H5;subst.
             SLSolve.
             simpl. lia.
           +++ (* with *)
             eapply IH with (m:= complexityL (F::L)) (L:= F ::L) (L' := F :: L') in H8;auto.
             eapply IH with (m:= complexityL (G::L)) (L := G :: L) (L' := G :: L') in H9;auto.
             simpl. lia.
             inversion H;subst.
             inversion H5;subst.
             SLSolve.
             simpl. lia.
             inversion H;subst.
             inversion H5;subst.
             change (F :: L') with ([F] ++ L').
             apply Forall_app;auto.           
           +++  (* quest *)
             eapply IH with (m:= complexityL L) (L' :=L') in H7;auto.
             lia.
             inversion H;subst;auto.
           +++  (* store *)
             eapply IH with (m:= complexityL L) (L' :=L') in H9;auto.
             assert (complexity l' > 0) by (apply Complexity0).
             lia.
             inversion H;subst;auto.
           +++ (* forall *)
             eapply tri_fx';auto;intros.
             generalize (H9 x H2);intro.
             eapply IH with (m:= complexity (FX x) + complexityL L) (L' := FX x :: L') in H4;auto.
             assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
             apply ComplexityUniformEq;auto.          
             constructor.
             lia.
             inversion H;subst.
             inversion H7;subst.
             change (FX x  :: L') with ([FX x ] ++ L').
             apply Forall_app;auto.
             
        ++
          destruct Heq as [L1 [L2 [L1' [L2' Heq]]]].
          destruct Heq as [Heq [Heq1 Heq2]];subst.
          
          inversion H0;subst.
          
          +++ (* top *)
            eapply EquivAuxTop with (M:= l' :: L1').
            rewrite app_comm_cons in H.  SLFormulaSolve.
          +++ (* bottom *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6 .
            simpl in H6. 
            apply EquivAuxBot with (M:= l' :: L1');auto.
            simpl in Heqw. inversion Heqw. auto.
            inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
            rewrite Permutation_midle.
            apply Permutation_cons;auto. 
            auto.
            
          +++ (* par *)
            eapply IH with (m:= complexityL (F :: G :: L1 ++ l' :: L2))
                           (L:=F :: G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ; G] ++ L2') in H6.
            apply seqtoSeqN in H6. destruct H6.
            eapply EquivAuxPar with (M:= l' :: L1');simpl;simpl in H2;eauto using seqNtoSeq.
            simpl in Heqw. inversion Heqw. simpl.  lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H9...
             apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H9...
            rewrite Permutation_midle. 
            rewrite Heq2. perm.
            auto.


          +++ (* with *)
            eapply IH with (m:= complexityL (F :: L1 ++ l' :: L2))
                           (L:=F :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ] ++ L2') in H7;auto .
            eapply IH with (m:= complexityL (G :: L1 ++ l' :: L2))
                           (L:=G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [G ] ++ L2') in H8;auto .
            
            apply EquivAuxWith with (M := l' :: L1'); simpl;auto.
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H10...
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H10...
            simpl.
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            
          +++ (* quest *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6;auto .
            apply seqtoSeqN in H6. destruct H6.   
            eapply EquivAuxQuest with (M := l' :: L1');simpl in H2.
            rewrite Permutation_app_comm. 
            eauto using seqNtoSeq.
            
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
            rewrite Permutation_midle. rewrite Heq2. perm.

          +++ (* copy *)
            eapply IH with (m:= complexityL(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H8;auto .

            eapply EquivAuxStore with (M:=l' :: L1');eauto.
            rewrite Permutation_app_comm;eauto. 
            inversion Heqw.
            assert (complexity l > 0) by (apply Complexity0).
            lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
            rewrite Permutation_midle. rewrite Heq2. perm.
          +++ (* forall *)
            
            
            assert(forall x, proper x -> |-- B; M; UP ((l' :: L1' ) ++ [FX x] ++ L2')).
            intros x pX.
            eapply IH with (m:= complexityL(FX x :: L1 ++ l' :: L2)) (L:=FX x :: L1 ++ l' :: L2)  ;auto.
            inversion Heqw.
            simpl. 
            assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
            
            apply ComplexityUniformEq;auto. 
            constructor. lia.
            
            inversion H;subst;auto.
            change ((l' :: L1') ++ [FX x] ++ L2') with ([l'] ++ L1' ++ [FX x] ++ L2').
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H12...
            rewrite Permutation_midle. rewrite Heq2. perm.

            assert(forall B  L L' M   FX, 
                      isFormulaL L -> uniform_oo FX ->  (forall x, proper x -> |-- B ; M ; UP (L ++ [FX x]++ L')) ->  |-- B ; M ;  UP (L ++ [F{FX}] ++ L')).
            intros.
            eapply EquivAuxForAll;auto.
            
            apply H3 in H2;auto.
            inversion H;subst.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.  SLFormulaSolve.
          
  Qed.

  Theorem EquivUpArrow2 : forall B L L' M ,
      isFormulaL L' ->
      (|-- B ; M ; UP L) -> Permutation L L' ->
      |-- B ; M ;  UP L'.
    intros.
    apply seqtoSeqN in H0.
    destruct H0.
    eapply EquivUpArrow in H0;eauto.
  Qed.



  Generalizable All Variables.
  Global Instance Forall_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (isNotAsyncL).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl;unfold isNotAsyncL.
    intros.
    rewrite <- H;eauto.
  Qed. 

  
  Lemma UpExtension: forall B M L F n,
      ~ asynchronous F ->
      (n |--- B; F::M ; UP L) ->
      exists m, m<= S n /\ m |--- B; M ; UP (L ++ [F]).
  Proof with subst;auto.
    intros.
    remember (complexityL L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .

    induction w as [| w' IH] using strongind .
    intros n M F HNA B L HD Hw.
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      { exists ((S n)). firstorder.
      simpl.
      eapply tri_store;auto. }
      simpl in Hw.
      apply exp_weight0LF in Hw;contradiction.
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* top *)
        exists 0%nat. 
        firstorder;[lia | eapply tri_top ].
      ++ (* bot *)
        apply IH with (m:= complexityL L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder;[lia | eapply tri_bot;auto ].
      ++  (* PAR *)
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_par;auto ].
        simpl. lia.
      ++ (* with *)
        apply IH with (m:= complexity  F0 + complexityL  L) in H6;try lia;auto.
        apply IH with (m:= complexity  G + complexityL L) in H7;try lia;auto.
        destruct H6 as [n'  [IHn IHd]].
        destruct H7 as [m'  [IHn' IHd']].
        simpl.
        exists (S (S n0)).
        firstorder; eapply tri_with;auto.
        eapply HeightGeq with (n:=n');try firstorder.  
       eapply HeightGeq with (n:=m');try firstorder.  
      ++  (* quest *)
        apply IH with (m:= complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_quest;auto ]. 
        lia.
      ++ (* Store *)
        assert(exists m0 : nat, m0 <= S n0 /\ m0 |--- B; M ++ [o]; UP (L ++ [F])).
        apply IH with (m:= complexityL L);auto.
        assert (complexity o > 0) by (apply Complexity0);lia.
        eapply exchangeLCN;[|exact H7].
        perm.
        
        destruct H1 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_store;[auto | LLExact IHd] ].
     ++  (* FORALL *)
        assert(forall x, proper x -> exists m, m <= S n0 /\  m |--- B; M; UP ((FX x :: L)  ++ [F])).
        intros.
        generalize (H7 x H1);intro.
        eapply IH with (m:=complexity (FX x) + complexityL L);auto.
        assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
        
        apply ComplexityUniformEq;auto. 
        
        constructor.
        lia.
        
        simpl.
        exists (S (S n0)). 
        split ; [auto|eapply tri_fx;auto;intros].
        
        generalize (H1 _ H2);intro.
        
        destruct H3 as [n H3].
        destruct H3 as [H3 H3'].
        eapply @HeightGeq with (n:=n);try firstorder.
       
  Qed.
  
    Lemma UpExtension': forall B M L F,
      ~ asynchronous F ->
      (|-- B; F::M ; UP L) -> |-- B; M ; UP (L ++ [F]).
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply UpExtension in H0...
  apply seqNtoSeq in H2...
  Qed.

Lemma UpExtensionInv n F B M L :
     n |---  B ; M ; (UP (L++[F])) -> |-- B ; F::M; (UP L).
  Proof with sauto;solveF;solveLL.
  intros.
  
  revert dependent F. 
  revert B M L.
  induction n using strongind;intros...
  + inversion H...
    apply ListConsApp in H4...
    decide1 top M.
  + inversion H0... 
    -
    apply ListConsApp in H5...
    decide1 top M.
    -
    apply ListConsApp in H2...
    decide1 bot M.
    apply seqNtoSeq in H5...
    eapply H in H5...
    -
    apply ListConsApp in H2...
    decide1 (F0 $ G) M.
    apply seqNtoSeq in H5...
    rewrite app_comm_cons in H5.
    rewrite app_comm_cons in H5. 
    eapply H in H5...
    -
    apply ListConsApp in H2...
    decide1 (F0 & G) M.
    apply seqNtoSeq in H3...
    apply seqNtoSeq in H6...
    rewrite app_comm_cons in H3. 
    eapply H in H3...    
    rewrite app_comm_cons in H6.
    eapply H in H6...
    -
    apply ListConsApp in H2...
    decide1 (i ? F0) M.
    apply seqNtoSeq in H5...
    eapply H in H5...
    -
    apply ListConsApp in H2...
    apply seqNtoSeq in H6;auto.
    eapply H in H6...
    LLExact H6.        
    - 
    apply ListConsApp in H2...
    decide1 (F{ FX}) M.
    apply H6 in properX...
    apply seqNtoSeq in properX...
    apply H6 in properX...
    rewrite app_comm_cons in properX.
    eapply H in properX...
 Qed. 


Lemma UpExtensionInvN n F B M L :
     n |---  B ; M ; (UP (L++[F])) -> S (S n) |--- B ; F::M; (UP L).
  Proof with sauto;solveF;solveLL.
  intros.
  revert dependent F. 
  revert B M L.
  induction n using strongind;intros...
  + inversion H...
    apply ListConsApp in H4...
    decide1 top M.
  + inversion H0...
    -
    apply ListConsApp in H5...
    decide1 top M.
    -
    apply ListConsApp in H2...
    decide1 bot M.
    -
    apply ListConsApp in H2...
    decide1 (F0 $ G) M.
    -
    apply ListConsApp in H2...
    decide1 (F0 & G) M.
    -
    apply ListConsApp in H2...
    decide1 (i ? F0) M.
    -
    apply ListConsApp in H2...
    LLExact H6.
    apply (exchangeLCN (perm_swap F0 F M))...
    -
    apply ListConsApp in H2...
    decide1 (F{ FX}) M.
    apply H6 in properX...
 Qed. 
 
  Lemma UpExtensionInv' F B M L : 
       |--  B ; M ; (UP (L++[F])) -> |-- B ; F::M; (UP L).
  Proof with sauto.
  intros.
  apply seqtoSeqN in H.
  destruct H.
  apply UpExtensionInv in H... 
  Qed.
 

Lemma UpExtensionInv2 n F B M L1 L2 :
   ~ asynchronous F ->  n |---  B ; M ; (UP (L1++[F]++L2)) -> |-- B ; F::M; (UP (L1++L2)).
  Proof with sauto;solveF;solveLL.
  intros.
  apply UpExtensionInv'.
  
  rewrite app_assoc_reverse.
  revert dependent F. 
  revert B M L1 L2.
  induction n using strongind;intros...
  + inversion H0...
    apply ListConsApp' in H5...
  + inversion H1...
    -
    apply ListConsApp' in H6...
    -
    apply ListConsApp' in H3...
    eapply H in H6...
    -
    apply ListConsApp' in H3...
    rewrite app_comm_cons in H6.
    rewrite app_comm_cons in H6. 
    eapply H in H6...
    -
    apply ListConsApp' in H3...
    rewrite app_comm_cons in H4. 
    eapply H in H4...    
    rewrite app_comm_cons in H7.
    eapply H in H7...
    -
    apply ListConsApp' in H3...
    eapply H in H6...
    -
    apply ListConsApp' in H3...
    apply seqNtoSeq in H7...
    apply UpExtension';auto.
    eapply H in H7...        
    -
    apply ListConsApp' in H3...
    apply H7 in properX...
    rewrite app_comm_cons in properX.
    eapply H in properX...
 Qed. 
 
End InvNPhase.
