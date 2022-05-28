
(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export MMLL.Misc.Utils. 
Require Export MMLL.Misc.Permutations. 
Require Export MMLL.SL.FLLTacticsPre.
Require Import Coq.Program.Equality.

Export ListNotations.
Export LLNotations .
Set Implicit Arguments.


Section FLLBasicTheory.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.

  Section StructuralProperties.
    Variable theory : oo -> Prop. (* Theory Definition *)
    
    Notation " n '|-F-' B ';' L ';' X " := (seqN theory n B L X)  (at level 80).
    Hint Constructors seqN : core .
    Notation " '|-f-' B ';' L ';' X " := (seq theory B L X)  (at level 80).
    Notation " n '|-F-' B '/' a '/' D ';' L ';' X " := (tri_bangK4 theory n B a D L X)  (at level 80).
    
    Notation " '|-f-' B '/' a '/' D ';' L ';' X " := (tri_bangK4' theory B a D L X)  (at level 80).
     
    Hint Constructors seqN : core.
    Hint Constructors seq : core.
   
    Theorem WeakTheoryN_mutual : forall n a B CC LC X (th th':oo->Prop),
        (forall F, th F -> th' F) ->
        (seqN th n CC LC X -> seqN th' n CC LC X) /\
        (tri_bangK4 th n B a CC LC X -> tri_bangK4 th' n B a CC LC X).
    Proof with sauto.    
      induction n using strongind;intros.
      + split;intros; 
        inversion H0;eauto.
      + split;intros.
        - assert(Hyp : forall m : nat,
    m <= n ->
    forall (a : subexp)
      (B CC : list TypedFormula)
      (LC : multiset oo) (X : Arrow),
    (seqN th m CC LC X ->
     seqN th' m CC LC X)).
     intros...
     eapply H with (th:=th)...
     inversion H1; subst. 
     
     1-20: eauto using Hyp.
     apply tri_bang...
     eapply H with (th:=th)...
     createWorld i.
     eapply H with (th:=th)...
     - inversion H1...
       copyK4 b F B'. 
       eapply H with (th:=th)...
       copyUK b F B'. 
       eapply H with (th:=th)...
       copyLK b F B'. 
       eapply H with (th:=th)...
       finishExp.
       eapply H with (th:=th)...
  Qed.     
 
 Theorem WeakTheoryN : forall n CC LC X (th th':oo->Prop),
        (forall F, th F -> th' F) ->
        (seqN th n CC LC X -> seqN th' n CC LC X).
    Proof with sauto.    
     intros.
     eapply WeakTheoryN_mutual...
     exact H.
     auto.
  Qed.     
  
  (**************** Exchange Rules ****************)
      
 Theorem exchangeLCN : forall n CC LC LC'  (X: Arrow),
        Permutation LC LC' ->
        (n |-F- CC ; LC ; X) -> n |-F- CC ; LC' ; X.
    Proof with sauto;solveLL.
      induction n using strongind;intros.
      + inversion H0 ...
      + inversion H1...
        LLTensor M N B D. 
        1-8: eauto.
        eapply H;eauto using Permutation_app_tail.

        LFocus F L'...
        all:eauto.
     Qed.

  Theorem exchangeLC LC : forall CC LC'  (X: Arrow),
        Permutation LC LC' ->
        ( |-f- CC ; LC ; X) -> |-f- CC ; LC' ; X.
    Proof with sauto;solveLL.
    intros.
    revert dependent LC'.
    induction H0;intros...
    * LLTensor M N B D.
    * LFocus F L'. 
    * UFocus i F.
    * BFocus i F. auto.
    * TFocus F.
    * LLExists t.
    * createWorld i.
  Qed.  
    
 Lemma exchangeCCNK4 : forall n CC CC' D O X i,
        Permutation CC CC' ->
        tri_bangK4 theory n CC i  D O  X ->
        tri_bangK4 theory n CC' i  D O X.
  Proof with sauto.
  intros *.
  intros Hp Hseq.
  generalize dependent CC'.
  induction Hseq;intros;eauto using Permutation_in.
  * copyK4 b F B'...
  * copyUK b F B'...
  * copyLK b F B'...    
  * rewrite Hp in H.
    finishExp...
 Qed.  
   
   Lemma exchangeCCK4 : forall CC CC' D O X i,
        Permutation CC CC' ->
        tri_bangK4' theory CC i D O X ->
        tri_bangK4' theory CC' i D O X.
  Proof with sauto .
  intros *.
  intros Hp Hseq.
  generalize dependent CC'.
  induction Hseq;intros;eauto using Permutation_in.
  * copyK4 b F B'... 
  * copyUK b F B'... 
  * copyLK b F B'... 
  * rewrite Hp in H.
    finishExp...
 Qed.  
 
 Lemma exchangeCCN : forall n CC CC' D (X:Arrow),
        Permutation CC CC' ->
        n |-F- CC ; D ; X ->
        n |-F- CC' ; D ; X.
  Proof with sauto.
  intro.
  induction n using strongind;intros.
  * inversion H0...
    - srewrite H in H1...
    - srewrite H in H3...
      solveLL.
    - srewrite H in H1... 
  * inversion H1...
    2-14: eauto using Permutation_in.
    5-10: eauto using Permutation_in.
    srewrite H0 in H2...
    srewrite H0 in H2...
    LLTensor M N B D0...
    rewrite <- H0...
    rewrite <- H0...
    rewrite <- H0...
    BFocus i F B'...
    rewrite H0 in H3.
    eapply tri_bangL...
    eapply H;eauto.
    apply tri_bang...
    eapply exchangeCCNK4 with (CC:=CC)...
   
    apply @tri_bangD with (i:=i)...
   
    eapply exchangeCCNK4 with (CC:=CC)...
    
   Qed.
 
 Lemma exchangeCC : forall CC CC' D (X:Arrow),
        Permutation CC CC' ->
        |-f- CC ; D ; X ->
        |-f- CC' ; D ; X.
  Proof with sauto.
  intros *.
  intros Hp Hseq.
  generalize dependent CC'.
  induction Hseq;intros...
  srewrite Hp in H...
  srewrite Hp in H1. solveLL.
  srewrite Hp in H...
  srewrite Hp in H...
  rewrite Hp in *...
  LLTensor M N B D. 
  eauto using Permutation_in. 
  eauto using Permutation_in. 
  BFocus i F B'...
  eauto using Permutation_in. 
  eauto using Permutation_in.
  eapply tri_bangL'...
  rewrite Hp in H;auto.
  eapply tri_bang'...
  eapply exchangeCCK4 with (CC:=B)...
  apply @tri_bangD' with (i:=i)...
  eapply exchangeCCK4 with (CC:=B)...

Qed. 
   
  Lemma exchangeCCNKK4 : forall n i CC CC' B D X,
        Permutation CC CC' ->
        tri_bangK4 theory n B i CC D X ->
         tri_bangK4 theory n B i CC' D X.
  Proof with sauto .
  intro.
  induction n using strongind;intros.
  * inversion H0. 
  * inversion H1...
        -- 
        copyK4 b F B'...
        eapply H with (CC:=CC ++ [(plust b, F)])... 
        rewrite <- H0...
        --
        copyUK b F B'...
        eapply H with (CC:=CC ++ [(loc, F)])...
        rewrite <- H0... 
        --
        copyLK b F B'...
        eapply H with (CC:=CC)...
       --
        finishExp. 
        eapply exchangeCCN with (CC:=CC)...
  Qed.
 

  Lemma exchangeCCKK4 : forall CC CC' i B D X,
        Permutation CC CC' ->
        tri_bangK4' theory B i CC D X ->
         tri_bangK4' theory B i CC' D X.
  Proof with sauto .
  intros.
  revert dependent CC'.
  induction H0;intros...
  * 
   copyK4 b F B'...
   eapply IHtri_bangK4'. rewrite H3. perm.
  * 
   copyUK b F B'...
   eapply IHtri_bangK4'. rewrite H4. perm.
  * 
   copyLK b F B'...
  *
   finishExp.
   eapply exchangeCC with (CC:=C)...
  Qed.
  
  Global Instance seq_morphismN  n:
      Proper ((@Permutation TypedFormula) ==> (@Permutation oo) ==> eq ==> iff)
             (seqN theory n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCCN H _);auto.
         refine (exchangeLCN H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCCN H _);auto.
        refine (exchangeLCN H0 _);auto.
    Qed.
   
   Global Instance seq_morphism  :
      Proper ((@Permutation TypedFormula) ==> (@Permutation oo) ==> eq ==> iff)
             (seq theory).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCC H _);auto.
         refine (exchangeLC H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCC H _);auto.
        refine (exchangeLC H0 _);auto.
    Qed.
    
   Global Instance seqK4_morphismN  n:
      Proper ((@Permutation TypedFormula) ==> eq ==> (@Permutation TypedFormula) ==> eq ==> eq ==> iff)
             (tri_bangK4 theory n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      + destruct y3. 
        refine (exchangeCCNK4 H _);auto.
        refine (exchangeCCNKK4 H1 _);auto.
        inversion H4.
      + apply Permutation_sym in H.
        apply Permutation_sym in H1.
        destruct y3. 
        refine (exchangeCCNK4 H _);auto.
        refine (exchangeCCNKK4 H1 _);auto.
        inversion H4.
    Qed.

     Global Instance seqK4_morphism :
      Proper ((@Permutation TypedFormula) ==> eq ==> (@Permutation TypedFormula) ==> eq ==> eq ==> iff)
             (tri_bangK4' theory).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      + destruct y3. 
        refine (exchangeCCK4 H _);auto.
        refine (exchangeCCKK4 H1 _);auto.
        inversion H4.
      + apply Permutation_sym in H.
        apply Permutation_sym in H1.
        destruct y3. 
        refine (exchangeCCK4 H _);auto.
        refine (exchangeCCKK4 H1 _);auto.
        inversion H4.
    Qed.
   
  (**************** End Exchange Rules ****************)
   
  (** We can generalize the exponential phase in order to 
     avoid mutual induction *)  
  
  Ltac classic_or_linear sub :=
    destruct(uDec sub);simplSignature1. 
    
    
 Theorem GenK4 n a B L O D C4 CK CN : 
  a <> loc -> LtX a C4 -> LtX a CK -> SetK4 C4 -> SetK CK -> Permutation B (C4++CK++CN) ->
  tri_bangK4 theory  (n - length (C4 ++ CK)) CN a (D++PlusT C4++Loc (getU CK)) O (UP (L ++ second (getL CK))) ->
    tri_bangK4 theory  n B a D O (UP L).
  Proof with  CleanContext.
    revert dependent L;
    revert dependent D;
    revert dependent O;
    revert dependent B;
    revert dependent CN;
    revert dependent CK;
    revert dependent n.
    induction C4;intros... 
    * simpl in *.
      revert dependent L;
      revert dependent D;
      revert dependent O;
      revert dependent B;
      revert dependent CN;
      revert dependent n.
      induction CK;intros;sauto.
      - cleanF.
        simplSignature1.
        sauto.
        apply (exchangeCCNK4 (symmetry H4))... 
      - destruct n.
        inversion H5. 
         destruct a0 as [b F]...
         classic_or_linear b. 
        + apply (exchangeCCNK4 (symmetry H4))...
           copyUK b F (CK++CN).
      
          eapply IHCK with (CN:=CN)...
          solveLT.
          solveSE.
          rewrite app_assoc_reverse...
        +  apply (exchangeCCNK4 (symmetry H4))...
          copyLK b F (CK++CN).
          
          eapply IHCK with (CN:=CN)...
          solveLT.
          solveSE.
          eapply exchangeCCNKK4 .
          2:{ simpl in H5. rewrite app_assoc_reverse. exact H5. }
          perm.
    * simpl in *...
      revert dependent L;
      revert dependent D;
      revert dependent O;
      revert dependent B;
      revert dependent CN;
      revert dependent n.
      induction CK;intros...
      - destruct n.
        inversion H5. 
        apply (exchangeCCNK4 (symmetry H4))...
        destruct a0 as [b F].
        copyK4 b F (C4++CN).
        eapply IHC4 with (CN:=CN) (CK:=[])...
        solveLT.
        solveSE.
        simpl...
        rewrite app_assoc_reverse...
      - simpl in H5...
        destruct n.
        inversion H5. 
        apply (exchangeCCNK4 (symmetry H4))...
        destruct a0 as [b0 F0].
        destruct a1 as [b1 F1]...
        copyK4 b0 F0 (C4++((b1, F1) :: CK) ++ CN). 
        eapply IHC4 with (CN:= CN) (CK:=(b1, F1)::CK)...
        solveLT.
        solveSE.
         rewrite app_assoc_reverse...
 Qed.
    
   
Theorem tri_exp_pred n a D O L CN: n >= 1 -> SetU CN ->
   n - 1 |-F- D; O; (UP L) ->  tri_bangK4 theory n CN a D O (UP L).
 Proof with simplifier;auto.
    destruct n;intros...
    inversion H.
    finishExp. 
 Qed.


Theorem tri_exp_pred_inv' a D O L :
   tri_bangK4' theory [] a D O (UP L) ->  |-f- D; O; (UP L).
 Proof with sauto.
 intros.
 inversion H...
Qed. 

(* GenK4Rel *)
 Theorem GenK4Rel n a B D O L CK C4 CN : 
  a <> loc -> SetK4 C4 -> SetK CK -> LtX a C4 -> LtX a CK -> SetU CN ->
     Permutation B (C4++CK++CN) ->
    n >= length (C4 ++ CK) + 1 -> 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc (getU CK) ; O ;(UP (L ++ second (getL CK)) ) -> 
    tri_bangK4 theory  n B a D O (UP L). 
Proof with subst;auto.
    intros.
    eapply GenK4 with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp_pred...
    lia.
 Qed.

 Theorem GenK4RelU n a B D O L CK C4 CN : 
     a <> loc -> SetK4 C4 -> SetK CK ->  LtX a C4 -> LtX a CK ->SetU CN ->
     Permutation B (C4++CK++CN) ->  SetU C4 -> SetU CK ->
    n >= length (C4 ++ CK) + 1 -> 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc CK ; O ;(UP L ) -> 
    tri_bangK4 theory  n B a D O (UP L). 
Proof with sauto.
    intros.
    eapply GenK4 with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp_pred...
    rewrite SetU_then_empty;simpl... 
    simplFix...
 Qed.
   
  Lemma InvSubExpPhase n a B L D O: 
   a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ n >= length (C4++CK) + 1  /\
        SetK4 C4 /\ SetK CK /\ SetU CN  /\ LtX a C4 /\ LtX a CK /\  
    n - length (C4++CK) - 1 |-F- (D++PlusT C4 ++ Loc (getU CK)) ; O ;(UP (L++ second (getL CK)) ).
    Proof with sauto.
    intros.
    revert dependent B;
    revert dependent D;
    revert dependent O;  
    revert dependent L;
    revert dependent a.
    induction n using strongind;intros...
    * inversion H0.
    * inversion H1...
      - eapply H in H11...
        clear H.
        eexists ([(b, F)] ++ x).
        eexists x0.
        eexists x1...
        rewrite <- H6.
        rewrite H3...
        simpl...
        simpl...
        simpl...
             eapply exchangeCCN.
        2:{ exact H14. }
        simpl. perm.
      - eapply H in H12...
        clear H.
        eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1. 
        rewrite <- H7.
        rewrite H3...
        simpl.
        rewrite <- Permutation_middle.
        simpl... 
        simpl... 
        simpl... 
        simpl.
        rewrite <- Permutation_middle.
        simpl...
        simpl.
        eapply exchangeCCN.
        2:{  exact H15. }
         perm.
   - eapply H in H12...
        clear H.
        
        eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1... 
        rewrite <- H7.
        rewrite H3. perm.
        simpl.
        rewrite <- Permutation_middle.
        simpl...
        simpl...
        simpl...
        simpl...  
        rewrite <- Permutation_middle.
        simpl...
        rewrite app_assoc_reverse in H15.
        eapply exchangeCCN.
        2:{ exact H15. }
        perm.
      - 
        eexists [].
        eexists [].
        eexists B...
        simpl...
        simpl...
    Qed.  
      
 Lemma InvSubExpPhaseLoc n B L D O: 
   tri_bangK4 theory n B loc D O (UP L) ->
   exists CK CN, Permutation B ((Loc (getU CK))++CN) /\ n >= length CK + 1  /\
        SetU CN  /\ 
    n - length (CK) - 1 |-F- (D++Loc (getU CK)) ; O ;(UP L).
    Proof with sauto.
    intros.
    revert dependent B;
    revert dependent D;
    revert dependent O;  
    revert dependent L. 
    induction n using strongind;intros...
    * inversion H.
    * inversion H0...
      - assert(b = loc).
        apply locAlone'...
        subst. solveSubExp.
      - assert(b = loc).
        apply locAlone'...
        subst. 
        eapply H in H11...
        clear H...
        eexists ([(loc, F)] ++ x).
        eexists x0.
        split;auto. 
        rewrite <- H6.
        rewrite H2.
        simpl...
        split;auto.
        simpl. lia.
        split;auto.
        simpl... eapply exchangeCCN.
        2:{ exact H10. }
        simpl. perm.
      - assert(b = loc).
        apply locAlone'...
        subst.
        solveSubExp.
      - exists []. 
        exists B...
        simpl... simpl...
      Qed.  

 Lemma InvSubExpPhaseU n a B D O L: 
  u a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1...
    assert(SetU x0).
    eauto with ExBase.
    assert(SetU x).
    eauto with ExBase.
    simplEmpty.
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H10...
    simplFix... 
 Qed.

Lemma InvSubExpPhaseSU n a B D O L: 
  SetU B -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1...
    assert(SetU (x ++ x0 ++ x1)) by solveLocation.
    assert(SetU (x0 ++ x1)) by solveLocation.
    assert(SetU x) by solveLocation. 
     assert(SetU x1) by solveLocation.
     assert(SetU x0) by solveLocation.
    eexists x.
    eexists x0.
    eexists x1...
    simplEmpty...
    simplFix...
    simpl in H10...
 Qed.

  Lemma InvSubExpPhaseK4 n a B D O L: 
  m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ n >= length C4 + 1 /\  SetU CN /\ 
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1... 
    simplEmpty...
    simpl in H10...
    exists x.
    exists x1...
   Qed.  


  Lemma InvSubExpPhaseUK4 n a B D O L: 
  u a = true -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ 
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4 in H2...
    exists x.
    exists x0...
    eapply SetUKClosure with (i:=a);auto.
   Qed.
   
  Lemma InvSubExpPhaseSUK4 n a B D O L: 
  SetU B -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ 
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4 in H2... 
    assert(SetU (x ++ x0)) by solveLocation. 
    exists x.
    exists x0...
    solveLocation.
   Qed. 
   
 Lemma InvSubExpPhaseUT n a B D O L: 
  u a =  true -> mt a = true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetU CN /\ SetT C4 /\ SetT CK /\ 
    n - length (C4 ++ CK) - 1 |-F- D++ C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseU in H2...
    assert(SetT x0).
    refine(SetTKClosure _ mt _ mtClosure H0 H7). 
    assert(SetT x).
    refine(SetTKClosure _ mt _ mtClosure H0 H6). 
  simplEmpty.
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H11...
    simplFix...  
 Qed.

Lemma InvSubExpPhaseSUT n a B D O L: 
  SetU B -> SetT B -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetT C4 /\ SetT CK  /\ SetU CN /\ 
    n - length (C4 ++ CK) - 1 |-F- D++ C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSU in H2...
    assert(SetT (x ++ x0 ++ x1)) by solveLocation.
    assert(SetT (x0 ++ x1)) by solveLocation.
    assert(SetT x) by solveLocation. 
     assert(SetT x1) by solveLocation.
     assert(SetT x0) by solveLocation.

    eexists x.
    eexists x0.
    eexists x1...
    simplEmpty...
    simplFix...
 Qed.


  Lemma InvSubExpPhaseUTK4 n a B D O L: 
  u a = true -> mt a = true -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ SetT C4 /\ 
    n - length C4 - 1 |-F- D++ C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseUK4 in H3...
    assert(SetT x).
    refine(SetTKClosure _ mt _ mtClosure H0 H5). 
    exists x.
    exists x0...
    simplFix...
   Qed.
   
  Lemma InvSubExpPhaseSUTK4 n a B D O L: 
  SetU B -> SetT B -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ SetT C4 /\  
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSUK4 in H3...
    assert(SetT (x ++ x0)) by solveLocation. 
    exists x.
    exists x0...
    solveLocation.
   Qed. 
     

 (** Same results for the system without height *)
 Theorem GenK4' a B L O D C4 CK CN : 
  a <> loc -> SetK4 C4 -> SetK CK ->  LtX a C4 -> LtX a CK ->Permutation B (C4++CK++CN) ->
  tri_bangK4' theory  CN a (D++PlusT C4++ Loc (getU CK)) O (UP (L ++ second (getL CK))) ->
    tri_bangK4' theory  B a D O (UP L).
  Proof with sauto.
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
      revert dependent CK.
   
     induction C4;intros... 
    * 
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
    induction CK;intros...
    simpl in H5.
     symmetry in H4.
      apply (exchangeCCK4 H4)...

     symmetry in H4.
     apply (exchangeCCK4 H4).
     destruct a0 as [b F].
     classic_or_linear b.
        + copyUK b F (CK++CN).
          eapply IHCK with (CN:=CN)... 
          solveSE.
          solveLT.
          rewrite app_assoc_reverse...
        + copyLK b F (CK++CN).
          eapply IHCK with (CN:=CN)... 
          solveSE.
          solveLT.
          simpl in H5. rewrite app_assoc_reverse. exact H5.
     *
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
    induction CK;intros... 
    symmetry in H4.
    apply (exchangeCCK4 H4)...
    destruct a0 as [b F].
    copyK4 b F (C4++CN).
    eapply IHC4 with (CN:=CN) (CK:=[])... 
    solveSE.
    solveLT.
    simpl in H5...
    simpl... 
    eapply exchangeCCKK4.
     2:{ exact H5. }
     perm. 

     symmetry in H4.
      apply (exchangeCCK4 H4)...

     destruct a0 as [b0 F0];
     destruct a1 as [b1 F1].
     
     copyK4 b0 F0 (C4++((b1, F1) :: CK) ++ CN).
     
     eapply IHC4 with (CN:= CN) (CK:=(b1, F1)::CK)... 
     solveSE.
     solveLT.
     eapply exchangeCCKK4.
     2:{ exact H5. }
     simpl. perm.
    Qed.
    
 Theorem GenK4Rel' a B D O L CK C4 CN : 
  a <> loc -> SetK4 C4 -> SetK CK -> LtX a C4 -> LtX a CK -> SetU CN  -> 
     Permutation B (C4++CK++CN) ->
    |-f- D++PlusT C4 ++ Loc (getU CK) ; O ;(UP (L ++ second (getL CK) )) ->
    tri_bangK4' theory B a D O (UP L). 
    Proof with subst;auto.
    intros.
    eapply GenK4' with (C4:=C4) (CK:=CK) (CN:= CN)...
    eapply tri_exp'...
  Qed.
  
 Theorem GenK4RelU' a B D O L CK C4 CN : 
     a <> loc -> SetK4 C4 -> SetK CK -> LtX a C4 -> LtX a CK -> SetU CN -> 
     Permutation B (C4++CK++CN) ->  SetU C4 -> SetU CK ->
    |-f- D++PlusT C4 ++ Loc CK ; O ;(UP L ) -> 
    tri_bangK4' theory B a D O (UP L). 
Proof with sauto.
    intros.
    eapply GenK4' with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp'...
    rewrite SetU_then_empty;simpl...
    simplFix... 
 Qed.

Theorem GenK4RelUT' a B D O L CK C4 CN : 
     a <> loc -> SetK4 C4 -> SetT C4 -> SetK CK -> LtX a C4 -> LtX a CK -> SetU CN -> 
     Permutation B (C4++CK++CN) ->  SetU C4 -> SetU CK ->
    |-f- D++ C4 ++ Loc CK ; O ;(UP L ) -> 
    tri_bangK4' theory B a D O (UP L). 
Proof with sauto.
    intros.
    eapply GenK4RelU' with (C4:=C4) (CK:=CK) (CN:= CN)...
    simplFix... 
 Qed.

  Lemma InvSubExpPhase' a B L D O: 
   a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\
        SetK4 C4 /\ SetK CK /\  LtX a C4 /\ LtX a CK /\ SetU CN /\  
     |-f- (D++PlusT C4 ++ Loc (getU CK)) ; O ;(UP (L++ second (getL CK)) ).
    Proof with sauto.
    intros.
    dependent induction H0...
                
    edestruct IHtri_bangK4'...
     eexists ([(b, F)] ++ x).
        eexists x0.
        eexists x1... 
    rewrite <- H1. rewrite H5. perm.
    simpl;solveSE.
    simpl;solveLT.
    eapply exchangeCC. 
    2:{ exact H12. } simpl. perm. 
     edestruct IHtri_bangK4'...
     eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1... 
    rewrite <- H2. rewrite H6. perm.
   simpl;solveSE.
    simpl;solveLT.
    simpl...
    eapply exchangeCC. 
    2:{ exact H13. } simpl;perm. 
    
    edestruct IHtri_bangK4'...
     eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1... 
    rewrite <- H2. rewrite H6. perm.
   simpl;solveSE.
    simpl;solveLT.
    simpl...
   
    rewrite (app_assoc_reverse L) in H13.
    exact H13.
    do 2 exists [].
    exists B...
    simpl...
    Qed.
 
  Lemma InvSubExpPhaseU' a B D O L: 
  u a =  true -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
   |-f- D++PlusT C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1... 
    assert(SetU x0).  
    { eapply SetUKClosure with (i:=a);auto. }
     assert(SetU x). 
    { eapply SetUKClosure with (i:=a);auto. } 
    simplEmpty...
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H9...
    simplFix...
 Qed.


 Lemma InvSubExpPhaseSU' a B D O L: 
  SetU B -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\   LtX a C4 /\ LtX a CK /\ SetU C4 /\ SetU CK  /\ SetU CN /\  
   |-f- D++PlusT C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1...
    
      assert(SetU (x ++ x0 ++ x1)) by solveLocation. 
      assert(SetU x) by solveLocation. 
      assert(SetU (x0++x1)) by solveLocation. 
      assert(SetU x0) by solveLocation. 
      assert(SetU x1) by solveLocation. 
      simplEmpty.
      exists x. exists x0. exists x1...
      simpl in H9...
      simplFix...
 Qed.

  Lemma InvSubExpPhaseK4'  a B D O L: 
  m4 a =  true -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ SetU CN /\  
    |-f- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1... 
    simplEmpty...
    simpl in H9.
    exists x.
    exists x1...
   Qed.  

 Lemma InvSubExpPhaseUK4'  a B D O L: 
 u a = true -> m4 a =  true -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ SetU CN /\  SetU C4 /\ 
    |-f- D++PlusT C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4' in H2... 
    exists x.
    exists x0...
     eapply SetUKClosure with (i:=a);auto.
   Qed.
  
 Lemma InvSubExpPhaseSUK4' a B D O L: 
  SetU B -> m4 a = true -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ SetU C4 /\ SetU CN /\ 
   |-f- D++PlusT C4; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSU' in H1... 
    simplEmpty... 
    simpl in H11.
    exists x.
    exists x1...
    solveSignature1...
  Qed.
   
  Lemma InvSubExpPhaseUT' a B D O L: 
  u a =  true -> mt a =  true -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\ LtX a C4 /\ LtX a CK /\  SetU C4 /\ SetU CK  /\ SetT C4 /\ SetT CK  /\ SetU CN /\ 
   |-f- D++C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
   intros.
    eapply InvSubExpPhaseU' in H2...
    assert(SetT x0).
    refine(SetTKClosure _ mt _ mtClosure H0 H7). 
    assert(SetT x).
    refine(SetTKClosure _ mt _ mtClosure H0 H6). 
  simplEmpty.
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H11...
    simplFix...  
 Qed.


 Lemma InvSubExpPhaseSUT' a B D O L: 
  SetU B -> SetT B -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 C4 /\ SetK CK /\   LtX a C4 /\ LtX a CK /\ SetU C4 /\ SetU CK  /\ SetU CN /\ SetT C4 /\ SetT CK  /\  
   |-f- D++ C4 ++ Loc CK ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSU' in H2...
    
      assert(SetT (x ++ x0 ++ x1)) by solveLocation. 
      assert(SetT x) by solveLocation. 
      assert(SetT (x0++x1)) by solveLocation. 
      assert(SetT x0) by solveLocation. 
      assert(SetT x1) by solveLocation. 
      simplEmpty.
      exists x. exists x0. exists x1...
      simplFix...
 Qed.

 Lemma InvSubExpPhaseUTK4'  a B D O L: 
 u a = true -> mt a = true -> m4 a =  true -> a <> loc -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ SetU CN /\  SetU C4 /\ SetT C4 /\ 
    |-f- D++ C4 ; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseUK4' in H3...
    assert(SetT x).
    refine(SetTKClosure _ mt _ mtClosure H0 H5). 
    exists x.
    exists x0...
    simplFix...
   Qed.
  
 Lemma InvSubExpPhaseSUTK4' a B D O L: 
  SetU B -> SetT B -> m4 a = true -> tri_bangK4' theory B a D O (UP L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 C4 /\ LtX a C4 /\ SetU C4 /\ SetT C4 /\ SetU CN /\ 
   |-f- D++ C4; O ;(UP L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSUK4' in H2...
    assert(SetT (x ++ x0)) by solveLocation.
    assert(SetT x) by solveLocation. 
    exists x.
    exists x0...
   simplFix...
  Qed.
      
 Theorem BangUnb n i BD M P: 
    u i = true -> n |-F- BD; M ; DW (Bang i P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0...
 inversion H2.
 apply InvSubExpPhaseU in H7...
 rewrite H2.
 solveLocation.
 Qed.
    
 Theorem BangUnb' i BD M P: 
    u i = true -> |-f- BD; M ; DW (Bang i P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0...
 inversion H2.
 apply InvSubExpPhaseU' in H6...
 rewrite H2.
 solveLocation.
 Qed.
 
          
 (* Soundness using mutuality *)
 Lemma seqNtoSeq_mutual : forall n a B D O L (X:Arrow),
    (tri_bangK4 theory n B a D O (UP L )  -> tri_bangK4' theory B a D O (UP L )) /\
    (seqN theory n B O X -> seq theory B O X).   
 Proof with subst;eauto. 
      induction n using strongind;intros;eauto.
      + split;intros.  
        - inversion H...
        - inversion H...
      + split;intros. 
        - inversion H0...
          { copyK4 b F B'...
            eapply H... }
          { copyUK b F B'...
            eapply H... }
          { copyLK b F B'...
            eapply H... }  
            
          finishExp.  
          eapply H... 
        - assert(Hp: forall m : nat,
                  m <= n ->
            forall  (B : list TypedFormula)
                    (O : multiset oo) (L : list oo) 
                    (X : Arrow),
           m |-F- B; O; X -> |-f- B; O; X).
           intros. eapply H...  
           
           inversion H0;subst. 
           1-20:eauto using Hp.
           apply tri_bang'...
           eapply H...
           firstorder.
           createWorld i.
           eapply H...
           firstorder.
Qed.       
                 
    
(* Soundness using inversion lemma of bang *)   
Lemma seqNtoSeq : forall n B C X,
    seqN theory n B C X -> seq theory B C X.
     Proof with sauto. 
      induction n using strongind;intros;eauto.
      + inversion H... eauto.
      + inversion H0... 
        1- 17: eauto.  
        apply InvSubExpPhase in H3...
        CleanContext.
        apply exchangeCC with (CC:=x ++ x0 ++ x1).
        rewrite H3. perm.
        createWorld.
        
        eapply GenK4' with (C4:=x) (CK:=x0)... 
        finishExp.
        eapply H with (m:=n - length (x ++ x0) - 1)... 
        eapply InvSubExpPhase in H2...
        CleanContext.
        createWorld i.
        eapply GenK4'  with (C4:=x) (CK:=x0)...
        solveSignature1.
        finishExp.
          
        eapply H with (m:=n - length (x ++ x0) - 1)...
        solveSignature1.
      Qed. 
 
 
   Lemma HeightGeq_mutual : forall n a B D O L (X:Arrow),
        (tri_bangK4 theory n B a D O (UP L) ->
        forall m, m>=n -> tri_bangK4 theory m B a D O (UP L)) /\
        (seqN theory n B O X ->
        forall m, m>=n -> seqN theory m B O X).
    Proof with sauto.
    intro.
      induction n;split;intros. 
      + inversion H ...
      + inversion H ... solveLL.
      + inversion H...
        - inversion H0... 
          copyK4 b F B'. 
          eapply IHn...
        - inversion H0... 
          copyUK b F B'. 
          eapply IHn...
        - inversion H0... 
          copyLK b F B'. 
          eapply IHn...
        - inversion H0... 
          finishExp.
          eapply IHn...
      + assert(Hp: forall B O (X : Arrow),
         seqN theory n B O X ->
         forall m : nat, m >= n -> seqN theory m B O X).
         intros. apply IHn;auto.
         inversion H;subst; try mgt0. 
         1-3:eauto.
         (* LLTensor *)
         LLTensor M N  B0 D0 . 
         eapply IHn;try lia ...
         eapply IHn;try lia ...
         1-9: intuition;eauto using Hp...
        (* dec *)
        LFocus F;eauto;eapply IHn;try lia...
        UFocus i F;eauto;eapply IHn;try lia...
        BFocus i F;eauto;eapply IHn;try lia...
        TFocus F;eauto;eapply IHn;try lia...
        LLExists t;eauto;eapply IHn;try lia...
        intuition;eauto using Hp...
        intuition;eauto using Hp...
        (* bang *)
        createWorld;auto;eapply IHn;try lia...
        firstorder.
        createWorld i;auto;eapply IHn;try lia...
        firstorder.
    Qed.    
    
     Lemma HeightGeq : forall n B O (X:Arrow),
        seqN theory n B O X ->
        forall m, m>=n -> seqN theory m B O X.
    Proof with sauto;solveLL.
    intros.
    eapply HeightGeq_mutual with (n:=n);auto...
     Qed. 
     
     
    (** HeightGeq with Exchange Classic Context *)
    Theorem HeightGeqCEx : forall n CC LC CC' X, 
        Permutation CC' CC ->
        (seqN theory n  CC LC X) ->
        forall m, m>=n -> (seqN theory m  CC' LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      eapply exchangeCCN;eauto.
    Qed.

    (** HeightGeq with Exchange Linear Context *)
    Theorem HeightGeqLEx : forall n CC LC LC' X, 
        Permutation LC LC' ->
        (seqN theory n  CC LC' X) ->
        forall m, m>=n -> (seqN theory m  CC LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      eapply exchangeLCN;eauto.
    Qed.  
    
   Theorem HeightGeqEx : forall n CC CC' LC LC' X, 
        Permutation CC CC' ->
        Permutation LC LC' ->
        (seqN theory n CC' LC' X) ->
        forall m, m>=n -> (seqN theory m CC LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      symmetry in H0.
      eapply exchangeLCN;eauto.
      eapply exchangeCCN;eauto.
    Qed.  
 
   
 (* Weakeness using mutuality *)   
  Lemma weakeness_mutual : forall n i CC LC D O F L X,
    u (fst F)= true ->
    (tri_bangK4 theory n CC i D O (UP L) ->
    tri_bangK4 theory n (CC) i (D++[F]) O (UP L)) /\
    (tri_bangK4 theory n CC i D O (UP L) ->
    tri_bangK4 theory n (CC++[F]) i (D) O (UP L)) /\    
    (n |-F- CC ; LC ; X -> n |-F- F :: CC ; LC ; X).
   Proof with sauto; try solveLL.   
      induction n using strongind;intros.
   * split;intros;[| 
       split;intros].  
     - inversion H0.
     - inversion H0.
     - inversion H0...
       init2 i0 (F::C).
       rewrite <- H3...
   * split;intros;[| 
       split;intros].  
      - inversion H1...
       { copyK4 b F0 B'...
         eapply exchangeCCNKK4 with (CC:=(D ++ [(plust b, F0)]) ++ [F])...
         eapply H... } 
       {  
         copyUK b F0 B'...
         eapply exchangeCCNKK4 with (CC:=(D ++[(loc, F0)]) ++ [F])...
         eapply H... }
       {  
         copyLK b F0 B'...
          eapply H... }         
       {  
         finishExp.
         eapply exchangeCCN with (CC:=F::D)...
         eapply H ... } 
     - inversion H1...
       { copyK4 b F0 (B'++[F])...
           rewrite <- H6...
         eapply H... } 
       {  
         copyUK b F0 (B'++[F])...
         rewrite <- H7...
         eapply H... }
       {  
         copyLK b F0 (B'++[F])...
         rewrite <- H7...
         eapply H... }         
       {  finishExp... solveLocation. }      
      - 
        assert(HX : forall m : nat,
               m <= n ->
              forall CC LC (X : Arrow),
               m |-F- CC; LC; X -> m |-F- F :: CC; LC; X).
        intros.
        eapply H...       
        
        inversion H1...
        init2 i0 (F::C).
        rewrite <- H4...
        destruct F; simpl in *.
        LLTensor M N ((s,o)::B) ((s,o)::D0)...
        1-3:simpl...
        eapply exchangeCCN with (CC:=F::(i0,F0)::CC)...
        eauto using HX .
        
        UFocus i0 F0...
        BFocus i0 F0 (F::B')...
        rewrite <- H6...
        TFocus F0. 
        LLExists t.
        createWorld. 
               eapply exchangeCCNK4 with (CC:=CC++[F])...
        eapply H...
        firstorder.
        createWorld i0.
    eapply exchangeCCNK4 with (CC:=CC++[F])...
        eapply H... firstorder.
   Qed.     
 
  Lemma weakeness_mutualGen X: forall n i CC D O L,
    SetU X ->
    tri_bangK4 theory n CC i D O (UP L) ->
    tri_bangK4 theory n (CC++X) i D O (UP L) .
   Proof with sauto.
   induction X;intros...
   eapply exchangeCCNK4 with (CC:=(CC++[a])++X)...
   apply IHX...
   solveLocation.
   apply weakeness_mutual...
   firstorder.
   simpl.
   solveSE.
   Qed.
  
    
  (**  Weakening using inversion lemma of bang *)
  Theorem weakeningN : forall n CC LC F X ,
      u (fst F) = true -> n |-F- CC ; LC ; X -> n |-F- F :: CC ; LC ; X.
   Proof with sauto;try solveLL.
    induction n using strongind;intros.
    * inversion H0...
      init2 i (F::C).
      rewrite <- H3...
    * inversion H1...
      init2 i (F::C).
      rewrite <- H4...
      LLTensor M N (F::B) (F::D)...
      destruct F as [a F]... 
      simpl...
      destruct F as [a F].
      simpl...
      destruct F as [a F].
      simpl...
      3: UFocus i F0... 
      3:{ BFocus i F0 (F::B')...
            rewrite <- H6... } 
      5:{
      apply InvSubExpPhase in H4... 
      createWorld. eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=F::x1);auto...
      rewrite H4. perm. }
     5:{
      apply InvSubExpPhase in H3...
      createWorld i.
      eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=F::x1);auto...
      solveSignature1.
      rewrite H3. perm. 
     solveSignature1.
       }
      all: eauto using Permutation_in...
        eapply exchangeCCN with (CC:=F::(i,F0)::CC)...
   Qed.    
     
    Theorem weakeningGenN CC LC  CC' X n:
      n |-F- CC ; LC ; X -> SetU CC' -> n |-F- CC'++ CC ; LC ; X.
    Proof.
      intros.
      induction CC';simpl;intros;auto.
      destruct a.
      apply weakeningN ;sauto.
      solveSE.
      apply IHCC'. solveSE.
    Qed.

    Theorem weakeningGenN_rev CC LC CC' X n:
      n |-F- CC ; LC ; X -> SetU CC' -> n |-F- CC++ CC' ; LC ; X.
    Proof.  
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
    Qed.
  
  
 
   
  Axiom seqtoSeqN : forall D O X, 
        seq theory  D O X -> exists n, (seqN theory n D O X).
  
  Lemma weakeness_mutual' : forall i CC  D O F L,
    u (fst F)= true ->
    (tri_bangK4' theory CC i D O (UP L) ->
    tri_bangK4' theory (CC++[F]) i (D) O (UP L)).
   Proof with sauto;try solveLL.
   intros.
   revert dependent F.
   induction H0;intros...
   * copyK4 b F (B'++ [F0])...
     rewrite <- H1...
   * copyUK b F (B'++ [F0])...
    rewrite <- H2...
   * copyLK b F (B'++ [F0])...
     rewrite <- H2... 
   * finishExp. solveLocation. 
   Qed.  
   
  
 Theorem seqtoSeqNK4 : forall i B D O X,
        (tri_bangK4' theory i B D O X) -> 
        exists n, (tri_bangK4 theory n i B D O X).
  Proof with sauto.
    induction 1 ;eauto;firstorder;eauto.
    + exists  (S x).
      copyK4 b F B'.
    + exists  (S x).
      copyUK b F B'.
    + exists  (S x).
      copyLK b F B'.
    +  apply seqtoSeqN in H0. 
      destruct H0.  
      exists (S x).
      finishExp.
  Qed.            

  
  Lemma weakeness_mutualGen' X: forall i CC D O L,
    SetU X ->
    tri_bangK4' theory CC i D O (UP L) ->
    tri_bangK4' theory (CC++X) i D O (UP L) .
   Proof with sauto.
   intros. 
   apply seqtoSeqNK4 in H0...
   eapply weakeness_mutualGen with (X:=X) in H0...
   apply seqNtoSeq_mutual in H0...
   firstorder.
   Qed.

         
    (**  Weakening on the classical context *)  
     Lemma weakening : forall CC LC F X ,
     u (fst F) = true -> |-f- CC ; LC ; X ->  |-f- F :: CC ; LC ; X.
    Proof with sauto.
    intros.
    revert dependent F.
    induction H0;intros...
    * init2 i (F::C).
      rewrite <- H1...
    * destruct F0...
      LLTensor M N ((s, o)::B) ((s, o)::D).
      simpl... simpl...
      simpl... 
    * solveLL.
      rewrite perm_swap...
    * LFocus F...
    * UFocus i F.
    * BFocus i F (F0::B'). rewrite <- H2...
    * TFocus F. 
    * LLExists t.
    * apply InvSubExpPhase' in H0... 
      createWorld.
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=F0::x1)...
      rewrite H2...
    * assert(i <> loc).
       solveSignature1.
      apply InvSubExpPhase' in H...
      createWorld i. 
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=F::x1)...
      rewrite H3... 
 Qed.     
   
    Theorem weakeningGen CC LC CC' X:
    SetU CC' -> |-f- CC ; LC ; X -> |-f- CC' ++ CC ; LC ; X.
    Proof with auto;try SLSolve. 
      induction CC';simpl;intros;auto.
      apply weakening... 
      solveSE.
      apply IHCC'...
      solveSE.
    Qed.
    
    Theorem weakeningAll CC LC X:
    SetU CC -> |-f- [] ; LC ; X -> |-f- CC ; LC ; X.
    Proof with auto. 
      intros. 
      rewrite <- (app_nil_r CC).
      apply weakeningGen...
    Qed.
    
    Theorem weakeningGen_rev CC LC CC' X :
      |-f- CC ; LC ; X -> SetU CC' -> |-f- CC++ CC' ; LC ; X.
    Proof.  
      intros.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
    Qed.
    

    (**  Exchange Rule: Classical Context *)
    Theorem exchangeCC' CC CC' LC (X: Arrow):
      Permutation CC CC' ->
    |-f- CC ; LC ; X -> |-f- CC' ; LC ; X.
     Proof with sauto. 
     intros.
     revert dependent CC'.
     induction H0;intros...
     * init1. rewrite <- H0... 
     * init2 i C.
     * LLOne.
       rewrite <- H0...
     * LLTensor M N B D. 
       rewrite <- H3...
       rewrite <- H3...
       rewrite <- H3...
     * LFocus F... 
     * UFocus i F.
       rewrite <- H4... 
     * BFocus i F B'.
     * TFocus F.
     * LLExists t.
     * LLBang. rewrite <- H1...
     * createWorld.
       rewrite <- H1...
     * assert(i <> loc).
      solveSignature1.
      apply InvSubExpPhase' in H...
      createWorld i. 
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=x1)...
    Qed.  
     
     Theorem weakeningGenSubSet CC LC CC' X:
    (exists Y, (Permutation CC' (CC++Y)) /\ SetU Y) ->
    |-f- CC ; LC ; X -> |-f- CC' ; LC ; X.
    Proof.
      intros.
      do 2 destruct H.
      assert(Permutation (x ++ CC) CC').
      rewrite H. perm.
      eapply (exchangeCC H2).
      apply weakeningGen;auto.
    Qed.
    
    
   
     
 Lemma lt_S n x :
  n >= S x -> n >= x.
 Proof.
    induction x;simpl;intros;
    [inversion H; lia | lia].
 Qed.
    (** Contraction on the classical context *)
   
  Lemma BangMax a n i B L P : lt a i -> 
  n |-F- B ; L ; (DW (Bang i P)) -> 
  n |-F- B ; L ; (DW (Bang a P)).
  Proof with CleanContext.
    intros.
    inversion H0...
    assert(a=loc).
    apply locAlone';auto.
    subst;auto.
    apply InvSubExpPhase in H7...
    
    assert(a <> loc).
    intro... solveSignature1. 
    createWorld.
    eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=x1)...
  Qed.
  
 
  End StructuralProperties.

  
  Definition EmptyTheory (F :oo) := False.
  Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      seqN EmptyTheory n CC LC X -> seqN theory n CC LC X.
  Proof with sauto. 
    intros.
    eapply @WeakTheoryN with (th:= EmptyTheory)...
    intros.
    inversion H0.
  Qed.
  
 
  (** Admissible rules including alternative definitions for the initial rule *)
  Section AdmissibleRules.
    Variable theory : oo -> Prop. 

Lemma Init2In th i A L (USB: UnbSignature): In (i, atom A) L -> mt i = true ->
seq th L [] (DW (perp A)).
Proof with sauto.
  intros.
  apply InPermutation in H...
  init2 i x.
Qed.

 Theorem InitPosNegN : forall Gamma A, SetU Gamma ->
        seqN theory 2 Gamma [atom A ; perp A ] (UP []).
      intros.
      solveLL.
    Qed.
    
    Theorem InitPosNegDwN : forall Gamma A, SetU Gamma ->
        seqN theory 4 Gamma [perp A ] (DW (atom A)).
      intros.
      solveLL.
    Qed.

    Theorem InitPosNeg : forall Gamma A,
    SetU Gamma -> seq theory Gamma [atom A ; perp A ] (UP []).
      intros.
      solveLL. 
    Qed. 

    Theorem InitPosNeg' : forall Gamma A,
     SetU Gamma -> seq theory Gamma [perp A ; atom A ] (UP []).
      intros.
      solveLL.
    Qed.
    
  End AdmissibleRules.

  (** Some simple invertibility lemmas *)
  Section Invertibility.
    Variable theory : oo -> Prop. (* Theory Definition *)


 Theorem FocusAtomN: forall n Gamma Delta A,
        (seqN theory n Gamma Delta (DW ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma /\ mt i = true).
    Proof with subst;auto.
      intros.
      inversion H ...
      2: inversion H1. 
      right.
      exists i;exists C;firstorder.
    Qed.


  Theorem FocusAtom: forall Gamma Delta A,
        (seq theory Gamma Delta (DW ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma /\ mt i = true).
  Proof with subst;auto.
      intros.
       inversion H ...
      2: inversion H1. 
      right.
      exists i;exists C;firstorder.
    Qed. 
 
  Theorem FocusAtomTensorN: forall n Gamma Delta A F,
        (seqN theory n Gamma Delta (DW (MAnd (perp A)  F))) -> 
       In (atom A) Delta \/  
        (exists i C D B, SetU C /\ seqN theory (n-1) D Delta (DW F) /\ seqN theory (n-1) B [] (DW (perp A)) /\
        Permutation ((i,atom A )::C) B /\ mt i = true /\ 
        Permutation (getU Gamma) (getU B) /\ 
        Permutation (getU Gamma) (getU D) /\ 
        Permutation (getL Gamma) (getL B ++ getL D) ).
    Proof with sauto.
      intros.
      inversion H ... 
      apply FocusAtomN in H9...
      - left. rewrite H2.
        simpl...
      - right.
        exists x.
        exists x0.
        exists D...
        exists B...
        eapply (exchangeLCN (symmetry H2))...
        init2 x x0.
      - inversion H1.
     Qed.   
    
    Theorem FocusAtomNUnb (SIU: UnbSignature): forall n Gamma Delta A,
        (seqN theory n Gamma Delta (DW ((perp A ) ))) ->
              Delta = [ (atom A)] \/ 
     (exists i, Delta = [] /\ In (i,atom A) Gamma /\ mt i = true).
    Proof with sauto.
      intros.
      inversion H ...
      2: inversion H1. 
      right.
      exists i...
      rewrite <- H6...
    Qed.


  Theorem InvTensorNUnb (SIU: UnbSignature) : forall n Gamma D F G,
   seqN theory n Gamma D (DW (MAnd F G)) ->
   exists M N, Permutation D (M++N) /\
   (seqN theory (n -1) Gamma M (DW F)) /\ 
   (seqN theory (n -1) Gamma N (DW G)).
  Proof with sauto.
  intros.
  inversion H...
  2: inversion H1. 
  exists M.
  exists N.
  split;auto.
  eapply simplUnb' in H3;[ | exact H5| solveSE ].
  eapply simplUnb in H4;[ | exact H5| solveSE ]...
  eapply (exchangeCCN (symmetry H3))...
  eapply (exchangeCCN (symmetry H4))...
   
  apply allSeTU...
  apply allSeTU...
  Qed.
   
    Theorem InvTensorNUnb' (SIU: UnbSignature) : forall n Gamma D F G,
   seqN theory n Gamma D (DW (MAnd F  G)) ->
   exists M N m, Permutation D (M++N) /\ S m <= n /\ 
   (seqN theory m Gamma M (DW F)) /\ 
   (seqN theory m Gamma N (DW G)).
  Proof with sauto.
  intros.
  inversion H...
  2: inversion H1. 
  exists M.
  exists N.
  exists n0.
  split;auto.
  split;auto.
  eapply simplUnb' in H3;[ | exact H5| apply allSeTU;auto
   ].
  eapply simplUnb in H4;[ | exact H5| apply allSeTU;auto ]...
  eapply (exchangeCCN (symmetry H3))...
  eapply (exchangeCCN (symmetry H4))...
  Qed.
   
    Theorem FocusAtomTensorInvN: forall n  A F,
        (seqN theory n []  [atom A] (DW (MAnd (perp A) F))) ->
        (seqN theory (sub n  1 ) [] [] (DW (F))).
    Proof with sauto.
      intros.
      inversion H... 
      * simpl in *.
        apply FocusAtomN in H9. 
        destruct H9.
        - destruct H0;subst. 
          inversion H1.
        - sauto.
         rewrite (cxtDestruct B) in H2...
      *  simpl in *...
         assert(D =[]).
         apply Permutation_nil.
         rewrite (cxtDestruct D)... 
         subst...
      * inversion H1.  
    Qed.   
    
    
    Theorem FocusAtomTensorTop: forall A B,
        (seq theory B [atom A] (DW (MAnd (perp A) Top))).
    Proof with sauto.
      intros.
      LLTensor [atom A] (@nil oo) (getU B) B...
      simplFix...
      simplEmpty...
      solveLL. auto with ExBase.
    Qed.  
    
    Theorem FocusTopOplus1: forall F B D,
        seq theory B D (DW (AOr Top F)).
    Proof with sauto.
      intros.
      solveLL.
    Qed.  
    
    Theorem FocusTopOplus2: forall F B D,
        seq theory B D (DW (AOr F Top )).
    Proof with sauto.
      intros.
      solveLL.
    Qed.  
   
    
  End Invertibility.

  Section GeneralResults.
    Variable theory : oo -> Prop. (* Theory Definition *)
    Hint Constructors seqN : core .
    Hint Constructors seq : core . 

    
  Lemma PProp_select B D CC F : Permutation (B++ getL D)
       (F :: CC) ->  u (fst F) = true -> 
       (exists L1' : list (subexp * oo),
        Permutation B (F :: L1') /\
        Permutation (L1' ++ getL D) CC).
  Proof with sauto.
   intros.
   checkPermutationCases H.
   exists x.
   split;auto.
   apply getLPerm_SetL in H1.
   assert(u (fst F) = false).   
   inversion H1...
   sauto.
   Qed.   


  Theorem contractionN  : forall n CC LC F X,
       u (fst F) = true -> seqN theory n (F :: CC) LC X -> In F CC -> seqN theory n CC LC X. 
  Proof with CleanContext;try solveLL.
  induction n using strongind;intros. 
  * inversion H0...
     solveSE.
    checkPermutationCases H4.
    apply InPermutation in H1...
    rewrite H7 in H2.
    rewrite H1 in H2. solveSE.
    init2 i x. rewrite H6 in H2. solveSE. solveSE.
   * inversion H1;sauto;solveLL;solveSE.
     
    checkPermutationCases H5.
    apply InPermutation in H2.
    destruct H2.
    init2 i x. rewrite H8 in H3.
    rewrite H2 in H3.
    solveSE.
    solveLL. rewrite H7 in H3. solveSE.
    
     destruct F... simpl in *...
   assert(In (s, o) D). 
    rewrite cxtDestruct.
    apply in_or_app.
    left. rewrite <- H6.
    firstorder.
    assert(In (s, o) B). 
    rewrite cxtDestruct.
    apply in_or_app.
    left. rewrite <- H5.
     firstorder.
    apply InPermutation in H3.
     destruct H3.
    apply InPermutation in H10.
     destruct H10.
 
    LLTensor M N x0 x...
  
    rewrite H10 in H5.
    simpl in H5...
    apply Permutation_cons_inv in H5;auto.
    rewrite H3 in H6.
    simpl in H6...
    apply Permutation_cons_inv in H6;auto.
    rewrite H10 in H7. rewrite H3 in H7.
    simpl in H7...
    eapply H with (F:=(s, o))...
    apply (exchangeCCN H10)...
    assert( Permutation (getU CC) (getU x0)).
    rewrite H10 in H5.
    simpl in H5...
    apply Permutation_cons_inv in H5;auto.
    assert(In (s, o) (getU CC)).
    apply uIngetU...
    rewrite H11 in H12.
    rewrite cxtDestruct.
    apply in_or_app.
    left...
     eapply H with (F:=(s, o))...
     apply (exchangeCCN H3)...
     assert( Permutation (getU CC) (getU x)).
    rewrite H3 in H6.
    simpl in H6... 
    apply Permutation_cons_inv in H6;auto.
    assert(In (s, o) (getU CC)).
    apply uIngetU...
    rewrite H11 in H12.
    rewrite cxtDestruct.
    apply in_or_app.
    left...
    1-7:eauto.
    apply H with (F:=F)...
      eapply exchangeCCN with (CC:=(i,F0)::F::CC)...
    1-2:eauto.
    inversion H7...
    UFocus i F0... 
    eapply H with (F:=(i, F0))...
    UFocus i F0...
    eapply H with (F:=F)...
    checkPermutationCases H7.
    simpl in H0...
    rewrite H7 in  H2.
    inversion H2...
    BFocus i F0 x...
    eapply H with (F:=F)...
    rewrite <- H9...
    
    1-4:eauto.
    -
    apply InPermutation in H2.
    destruct H2.
    apply InvSubExpPhase in H5;auto.
    destruct H5 as [C4 H5];
    destruct H5 as [CK H5];
    destruct H5 as [CN H5]...
    
    checkPermutationCases H3.
    (* F is in x or x0 or x1 *)
      + 
      rewrite H2 in H12.
      checkPermutationCases H12.
      --  createWorld. 
      apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=CN)...
          rewrite H12 in H5.
          rewrite H5 in H6...
          solveSE.
          rewrite H12 in H5.
          rewrite H5 in H10...
          solveLT.
          
          rewrite H2.
          rewrite <- H14...
          rewrite H5 in H7.
          rewrite <- H12...
          simpl in H7...
          eapply H with (F:=(plust (fst F), snd F)).
          lia.
          simpl... auto with ExBase.
          remember (n - length (x0 ++ CK) - 1) as Hh.
          rewrite H12 in HeqHh.
          simpl in HeqHh.
          eapply HeightGeqCEx.
          2:{ exact H13. }
          srewrite H5.
          srewrite H12.
          simpl. perm.
          rewrite H5 in H7.
          rewrite H12 in H7.
          subst. simpl in H7. 
          assert(Hs: n >= (S (length (x1 ++ CK) + 1))).
          apply lt_S...
          rewrite H5.
          rewrite H12.
          
          apply Nat.sub_le_mono_r... simpl... 
          firstorder.
      --  checkPermutationCases H12.
          ++
          rewrite H5 in H6.
          rewrite H12 in H8.
          
          inversion H8...
          inversion H6...
          ++
          createWorld.
          apply GenK4Rel with (C4:=F::x0) (CK:=CK) (CN:=x2)...
          srewrite H5 in H6...
          srewrite H5 in H10...
     
          rewrite H12 in H9... 
          solveSE. 
          
          rewrite H2.
          rewrite <- H14.
          rewrite <- H15... 
          
          rewrite H5 in H7.
          simpl in H7...
          simpl. 
          eapply HeightGeqCEx.
          2:{ exact H13. }
          rewrite H5.
          simpl... 
          rewrite H5. 
          simpl... 
    + rewrite H2 in H12.
      checkPermutationCases H12.
     --  checkPermutationCases H5.
         ++ rewrite H5 in H8.
            rewrite H12 in H6.
            inversion H6...
            inversion H8...
         ++ createWorld. apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=x2)...
           rewrite H12 in H6.
           solveSE.
           rewrite H12 in H10.
           solveLT.
           rewrite H5 in H9.
           solveSE.
            rewrite H2.
            rewrite <- H14.
            rewrite <- H15... 
            rewrite H12 in H7.
            simpl in H7...
            simpl. 
          eapply HeightGeqCEx.
          2:{ exact H13. }
          rewrite H12...
          rewrite H12...
     --  checkPermutationCases H5.
         ++ rewrite <- H15 in H12.
            checkPermutationCases H12.
            {
            assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
            
            apply Permutation_vs_cons_inv in H5;auto.
            sauto.
            assert(Permutation (x4 ++ F :: x5) (F :: x4 ++ x5)) by perm.
         assert( Permutation (C4 ++ x4 ++ F :: x5) (F :: C4 ++ x4 ++ x5)) by perm.
         rewrite H3 in H5.
          rewrite H17 in H13.
          createWorld.
            apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN);auto.
            rewrite <- Permutation_middle in H8.
            solveSE.
            rewrite <- Permutation_middle in H11.
            solveLT.
            rewrite H2.
            rewrite <- H14.
            rewrite <- H16...
            apply Permutation_cons_inv in H5.
            rewrite H5.
            rewrite H12...
            rewrite H17 in H7...
            simpl in H7...
            destruct F...
            eapply H with (F:=(loc, o))...
            solveSignature1. 
            setoid_rewrite getLApp in H13.
            simpl in H13...
            setoid_rewrite <- getLApp in H13.
           simpl...
            eapply HeightGeqCEx.
            2:{ exact H13. }
            rewrite <- Permutation_middle.
            simplCtx...
            simpl... rewrite <- getUApp...
            simpl...
            rewrite <- Permutation_middle...
            sauto.
            apply in_or_app.
            right. 
               rewrite H12 in H5.
            apply Permutation_cons_inv in H5.
            rewrite H5. 
            simpl... simpl... }
            {
            createWorld. 
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
           rewrite H12 in H9.
           solveSE.
           rewrite H2.
           rewrite <- H14.
           rewrite H5.
           rewrite <- H16...  }
      ++ rewrite <- H15 in H12.
         checkPermutationCases H12.
          {
            createWorld. 
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x2)...
           rewrite H5 in H9.
           solveSE.
           rewrite H2.
           rewrite <- H14.
           rewrite <- H16.
            rewrite H12... }
         
           {
            
           assert(tri_bangK4 theory n ((x++[F])) i [] [] (UP [F0])).
           eapply weakeness_mutual with (F:=F)...
           exact nil. firstorder.
           apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3)...
             rewrite H5 in H9.
             rewrite H12 in H9.
             inversion H9...
             inversion H19...
           rewrite <- H14.
           rewrite <- H16...
           createWorld.
           eapply exchangeCCNK4. 
           2:{  exact H3. }
           rewrite H2... }
-            
 apply InPermutation in H2.
    destruct H2.
    apply InvSubExpPhase in H4;auto.
    destruct H4 as [C4 H4];
    destruct H4 as [CK H4];
    destruct H4 as [CN H4]...
 
    checkPermutationCases H3.
    (* F is in x or x0 or x1 *)
    + 
      rewrite H2 in H12.
      checkPermutationCases H12.
      --  createWorld i.
          apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=CN)...
          solveSignature1.
          rewrite H4 in H6.
           solveSE.
          rewrite H12 in H6.
          solveSE.
          rewrite H4 in H10.
          rewrite H12 in H10.
          solveLT.
          rewrite H2. rewrite <- H14...
          rewrite H4 in H7.
          rewrite H12 in H7.
          simpl in H7.
          apply lt_S...
          simpl. 
          eapply H with (F:=(plust (fst F), snd F)).
          lia.
          simpl. auto with ExBase.
          remember (n - length (x0 ++ CK) - 1) as Hh.
          rewrite H12 in HeqHh.
          simpl in HeqHh.
          eapply HeightGeqCEx.
          2:{ exact H13. }
          rewrite H4.
          rewrite H12.
          simpl... 
          rewrite H4 in H7.
          rewrite H12 in H7.
          subst. simpl in H7. 
          assert(Hs: n >= (S (length (x1 ++ CK) + 1))).
          apply lt_S...
          rewrite H4.
          rewrite H12. 
          simpl...
          firstorder.
      --  checkPermutationCases H12.
          ++
          rewrite H4 in H6.
          rewrite H12 in H8.
          
          inversion H6...
          inversion H8...
          ++
          createWorld i.
          apply GenK4Rel with (C4:=F::x0) (CK:=CK) (CN:=x2)...
          solveSignature1.
          rewrite H4 in H6...
          rewrite H4 in H10...
          rewrite H12 in H9...
          solveSE.
           rewrite H2.
          rewrite <- H14.
          rewrite <- H15... 
          rewrite H4 in H7.
          simpl in H7...
          simpl. 
          eapply HeightGeqCEx.
          2:{ exact H13. }
          rewrite H4.
          simpl... 
          rewrite H4. 
          simpl... 
    + 
    rewrite H2 in H12.
      checkPermutationCases H12.
     --  checkPermutationCases H4.
         ++ rewrite H4 in H8.
            rewrite H12 in H6.
            inversion H6...
            inversion H8...
         ++
         createWorld i. 
            apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=x2)...
            
            solveSignature1.
            srewrite H12 in H6...
            srewrite H12 in H10...
            rewrite H4 in H9.
            solveSE.
            rewrite H2.
            rewrite <- H14.
            rewrite <- H15... 
            rewrite H12 in H7.
            simpl in H7...
            simpl. 
          eapply HeightGeqCEx.
          2:{ exact H13. }
          rewrite H12...
            rewrite H12...
     --  checkPermutationCases H4.
         ++ rewrite <- H15 in H12.
            checkPermutationCases H12.
            {
            assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
            
            apply Permutation_vs_cons_inv in H4;auto.
            sauto.
            assert(Permutation (x4 ++ F :: x5) (F :: x4 ++ x5)) by perm.
         assert( Permutation (C4 ++ x4 ++ F :: x5) (F :: C4 ++ x4 ++ x5)) by perm.
         rewrite H17 in H13.
          rewrite H17 in H7.
          createWorld i.
            apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN)...
             solveSignature1.
             rewrite <- Permutation_middle in H8.
             solveSE.
             rewrite <- Permutation_middle in H11.
             solveLT.
            rewrite H2. 
            rewrite <- H14.
            rewrite <- H16.
            rewrite <- Permutation_middle in H4.
            apply Permutation_cons_inv in H4.
            rewrite H4.
            rewrite H12...
            simpl in H7...
            destruct F.
            eapply H with (F:=(loc, o))...
            solveSignature1.
            setoid_rewrite getLApp in H13.
            simpl in H13...
            setoid_rewrite <- getLApp in H13.
            eapply HeightGeqCEx.
            2:{ exact H13. }
            rewrite <- Permutation_middle...
            simpl...
            simpl...
            apply in_or_app.
            right. 
            rewrite <- Permutation_middle in H4.
            apply Permutation_cons_inv in H4.
            rewrite H4.
            rewrite H12...
            simpl... simpl... }
            {
            createWorld i.
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3)... solveSignature1.
           rewrite H12 in H9.
           solveSE.
           rewrite H2.
           rewrite <- H14.
           rewrite H4.
           rewrite <- H16...  }
      ++ rewrite <- H15 in H12.
         checkPermutationCases H12.
          {
          createWorld i.
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x2)...
             solveSignature1. 
           rewrite H4 in H9.
           solveSE.
           rewrite H2.
           rewrite <- H14.
           rewrite <- H16.
            rewrite H12... }
         
           {
          
           assert(tri_bangK4 theory n ((x++[F])) i [] [] (UP [ ])).
           eapply weakeness_mutual with (F:=F)...
           exact nil. exact (UP nil).  
           apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3)...
            
            solveSignature1. 
             rewrite H4 in H9.
             rewrite H12 in H9.
             inversion H9...
           inversion H19...
             rewrite <- H14.
           rewrite <- H16...
           createWorld i.
           eapply exchangeCCNK4. 
           2:{  exact H3. }
           rewrite H2... }
      +  solveSignature1.      
               
 Qed.
 

 Theorem contractionK4N  : forall n i CC D LC F X, i <> loc -> 
       u (fst F) = true -> tri_bangK4 theory n (F :: CC) i D LC X -> In F CC -> 
       tri_bangK4 theory n CC i D LC X. 
Proof with sauto;try solveLL.
  intros. 
  destruct X.
  2: inversion H1.
    apply InvSubExpPhase in H1;auto.
    destruct H1 as [C4 H1];
    destruct H1 as [CK H1];
    destruct H1 as [CN H1]...
    
    checkPermutationCases H3.
  *  
    apply InPermutation in H2...
    rewrite H1 in H10.
     checkPermutationCases H10.
    -  
    apply GenK4Rel with (C4:=x) (CK:=CK) (CN:=CN)...
    rewrite H3 in H4.
    solveSE.
    rewrite H3 in H8.
    solveLT.
    rewrite H1.
    rewrite <- H12.
    rewrite H10...
    rewrite H3 in H5.
    simpl in H5...
    destruct F... 
    assert(u (fst(plust s,o)) = true).
    simpl.
    auto with ExBase. 
    eapply contractionN.
    exact H2.
    eapply HeightGeqCEx.
    2:{ exact H11. }
    rewrite H3...
    rewrite H3...
    simpl...
    apply in_or_app.
    right.  
    apply in_or_app.
    left.
    rewrite H10...
    simpl...
   - 
    checkPermutationCases H10.
    rewrite H3 in H4.
    rewrite H10 in H6.
    inversion H4.
    inversion H6...
    apply GenK4Rel with (C4:=C4) (CK:=CK) (CN:=x2)...
    rewrite H10 in H7. solveSE.
    rewrite H1.
    rewrite <- H12.
    rewrite <- H13.
    
    rewrite H3...
 *   
     apply InPermutation in H2...
    rewrite H1 in H10.
    checkPermutationCases H10.
   -
    checkPermutationCases H3.
    + rewrite H10 in H4.
      rewrite H3 in H6.
      inversion H4...
      inversion H6...
    +  
    apply GenK4Rel with (C4:=F::x1) (CK:= CK) (CN:=x2)...
    rewrite H10 in H4...
    rewrite H10 in H8...
    rewrite H3 in H7.
    solveSE.
    rewrite H1.
    rewrite <- H12.
    rewrite <- H13...
    rewrite H10 in H5...
    eapply HeightGeqCEx.
    2:{ exact H11. }
    rewrite H10...
    rewrite H10...
   - rewrite H10 in H3.  
     checkPermutationCases H3.
     + checkPermutationCases H13.
       assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
     {  apply Permutation_vs_cons_inv in H3;auto. }
     CleanContext.
     destruct F...
     assert(Permutation (x4 ++ (s, o) :: x5) ((s, o) :: x4 ++ x5)) by perm.
     assert( Permutation (C4 ++ x4 ++ (s, o) :: x5) ((s, o) :: C4 ++ x4 ++ x5)) by perm.
     rewrite H2 in H3.
     rewrite H2 in H6.
     rewrite H15 in *.
     clear H2 H15.
     apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN)...
     solveSE.
     rewrite <- Permutation_middle in H9.
     solveLT. 
     rewrite H1. 
     rewrite <- H12.
     rewrite <- H14.
     apply Permutation_cons_inv in H3.
     rewrite H3...
     rewrite H13...
     simpl in H5...
     setoid_rewrite getLApp in H11.
     simpl in H11...
    setoid_rewrite <- getLApp in H11.
     
    eapply contractionN  with (F:=(loc, o))...
    solveSignature1.
    eapply HeightGeqCEx.
    2:{ exact H11. }
    
    rewrite <- Permutation_middle.
    simpl... 
 simpl...   
    apply Permutation_cons_inv in H3.
    rewrite H3.
    rewrite H13. 
    apply in_or_app.
    right.
    apply in_or_app.
    right... 
    simpl... simpl...
      apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3)...
    rewrite H13 in H7.
    solveSE.  
    rewrite H1. rewrite <- H12. rewrite <- H14. rewrite H3...
   +  
  checkPermutationCases H13.
       assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
     {  apply Permutation_vs_cons_inv in H13;auto. }
     sauto.
     assert(Permutation (x4 ++ F  :: x5) (F :: x4 ++ x5)) by perm.
     assert( Permutation (C4 ++ x4 ++ F :: x5) (F :: C4 ++ x4 ++ x5)) by perm.
     
     rewrite H2 in H13.
     rewrite H2 in H6.
     rewrite H15 in H5 , H11.
     apply Permutation_cons_inv in H13.
     destruct F...
     apply GenK4Rel with (C4:=C4) (CK:=(s, o):: x4 ++ x5) (CN:=x2)...
     solveLT.
     rewrite H3 in H7. 
     solveSE.
     rewrite H1. 
     rewrite <- H12.
     rewrite <- H14.
     rewrite <- H13...
     rewrite <- Permutation_middle.
     simpl...
     rewrite <- Permutation_middle.
     setoid_rewrite getLApp in H11.
     simpl in H11...
     setoid_rewrite <- getLApp in H11.
      simpl...
     eapply HeightGeqCEx.
    2:{ exact H11. }
    simplCtx.
    simpl...
    setoid_rewrite locApp.
    simpl...
    lia.
    apply GenK4Rel with (C4:=C4) (CK:=CK) (CN:=x2)...
    rewrite H3 in H7.
    solveSE.
    rewrite H1.
    rewrite <- H12.
    rewrite <- H14.
    rewrite H13...
   Qed.  
 
                                                                                         
 Theorem contraction  : forall CC LC F X,
     u (fst F) = true -> seq theory (F :: CC) LC X -> In F CC -> seq theory  CC LC X. 
  Proof with subst;eauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply contractionN in H0...
  apply seqNtoSeq in H0...
 Qed.
 
  Theorem contractionK4  : forall i CC D LC F X, i <> loc -> 
       u (fst F) = true -> tri_bangK4' theory (F :: CC) i D LC X -> In F CC -> 
       tri_bangK4' theory CC i D LC X. 
Proof with sauto;try solveLL. 
  intros.
  destruct X...
  apply seqtoSeqNK4 in H1.
  destruct H1.
  apply contractionK4N in H1...
  eapply seqNtoSeq_mutual in H1...
  firstorder.
  inversion H1.
 Qed.
  
   Theorem contractionSet  : forall CC LC X L, (forall F, In F L -> In F CC) -> SetU L ->
        ( seq theory (L ++ CC) LC X) -> (seq theory CC LC  X).
   Proof.
      intros.
      induction L.
      simpl in H0;auto.
      apply IHL;intros.
      apply H. firstorder.
      solveSE.
      eapply exchangeCC with (CC':=a :: (L ++ CC)) in H1;[|auto].
      apply contraction in H1;auto.
      solveSE.
      apply in_or_app.
      firstorder.
  Qed.  

       
 Theorem contractionSetK4  : forall i CC LC D X L, i <> loc -> (forall F, In F L -> In F CC) -> SetU L ->
        (  tri_bangK4' theory (L ++ CC) i D LC X) -> tri_bangK4' theory CC i D LC X.
   Proof.
      intros.
      induction L.
      simpl in H0;auto.
      apply IHL;intros.
      apply H0. firstorder.
      solveSE.
      eapply exchangeCCK4 with (CC':=a :: (L ++ CC)) in H2;[|auto].
      apply contractionK4 in H2;auto.
      solveSE.
      apply in_or_app.
      firstorder.
  Qed.  
    
     Theorem contractionSet'  : forall  C1 C2 CC LC X, Permutation CC (C1++C2) -> SetU C1 ->
        ( seq theory (C1 ++ CC) LC X) -> (seq theory CC LC  X).
   Proof with sauto.
      intro.
      induction C1;intros.
      simpl in H0;auto.
      inversion H0...
      rewrite <- app_comm_cons in H1.
      apply contraction in H1;auto.
      
      eapply IHC1 with (C2:=a::C2) in H1...
      rewrite H...
      apply in_or_app.
      right. rewrite H.
      apply in_or_app.
      left.
      firstorder.
  Qed. 
  
    Theorem contractionGetU  : forall  C CC LC X, 
        ( seq theory (getU C ++ getU C ++ CC) LC X) -> (seq theory (getU C ++ CC) LC  X).
   Proof with sauto.
      intros.
      eapply contractionSet'
      with (C1:=getU C) (C2:=CC)...
      apply getUtoSetU.
  Qed. 
  
  Theorem contractionGetU_rev  : forall  C CC LC X, 
        ( seq theory (CC ++ getU C ++ getU C) LC X) -> (seq theory (CC ++ getU C) LC  X).
   Proof with sauto.
      intros.
      eapply contractionSet'
      with (C1:=getU C) (C2:=CC)...
      apply getUtoSetU.
      eapply exchangeCC.
      2:{ exact H. }
      perm.
  Qed.
 
 Theorem contractionGetUK4  : forall i C CC LC D X, i <> loc -> 
 ( tri_bangK4' theory (getU C ++ getU C ++ CC) i D LC X) -> tri_bangK4' theory (getU C ++ CC) i D LC X.
   Proof.
      intros.
      eapply contractionSetK4 with (L:=getU C);intros;eauto.
      apply in_or_app. left;auto.
      apply getUtoSetU.
  Qed.  
 
 Theorem contractionGetUK4_rev  : forall i C CC LC D X, i <> loc -> 
 ( tri_bangK4' theory (CC ++ getU C ++ getU C) i D LC X) -> tri_bangK4' theory (getU C ++ CC) i D LC X.
   Proof.
      intros.
      eapply contractionSetK4 with (L:=getU C);intros;eauto.
      apply in_or_app. left;auto.
      apply getUtoSetU.
      eapply exchangeCCK4.
      2:{ exact H0. }
      perm.
  Qed.  
    
  Lemma ContractionLoc : forall n i F B L X, 
   mt i = true -> u i = true -> seqN theory n ((loc,F)::(i,F)::B) L X -> 
   seqN theory n ((i,F)::B) L X.
  Proof with sauto;try solveLL.
  intro.
  induction n using strongind;intros... 
  * inversion H1...
     solveSE. 2:{ solveSE. }
    checkPermutationCases H4.
    init2 i B.
    rewrite H7 in H2.
    solveSE.
    checkPermutationCases H5.
    init2 i0 B.
    rewrite H6 in H2.
    rewrite <- H8 in H2.
    solveSE.
    init2 i0  ((i, F) :: x0).
    assert(SetU x0).
    rewrite H5 in H6. rewrite H6 in H2.
    inversion H2...
    inversion H10...
    apply Forall_cons...
    rewrite H7...
   * inversion H2...
   solveSE.
    checkPermutationCases H5.
    init2 i B. rewrite H8 in H3. solveSE.
    checkPermutationCases H6.
    init2 i0 B. 
    rewrite <- H9 in H7. rewrite H7 in H3.
    solveSE.
    init2 i0 ((i,F)::x0).
    rewrite H7 in H3.
    rewrite H6 in H3.
    solveSE.
    rewrite H8...
    solveSE.
    - 
     simpl in H5...
     simpl in H6...
     simpl in H7...
     simplSignature1.
     LLTensor M N (getU B ++ getL B0 ++ [(i, F)]) (getU B ++ getL D ++ [(i, F)])...
     do 2 simplCtx. simplEmpty.
     simplFix. simpl...
     do 2 simplCtx. simplEmpty.
     simplFix. simpl...
     do 2 simplCtx. simplEmpty.
     simplFix. simpl...
     
      rewrite app_assoc.
      rewrite Permutation_app_comm.
      simpl...
      eapply H...
      eapply exchangeCCN. 
      2:{ exact H8. }
      rewrite cxtDestruct.
      simplCtx.
      simplEmpty.
      simplFix...
      rewrite app_comm_cons.
      rewrite app_comm_cons.
      rewrite H5...
      
      rewrite app_assoc.
      rewrite Permutation_app_comm.
      simpl...
      eapply H...
      eapply exchangeCCN. 
      2:{ exact H9. }
      rewrite cxtDestruct.
      simplCtx.
      simplEmpty.
      simplFix...
      rewrite app_comm_cons.
      rewrite app_comm_cons.
      rewrite H6...
    - 
      rewrite perm_swap.  
      apply H...
      eapply exchangeCCN. 
      2:{ exact H4. }
      perm.
    - LFocus F0 L'. 
    - inversion H7...
      UFocus i F0.
      inversion H3... 
      UFocus i0 F0. 
      UFocus i0 F0.
    - checkPermutationCases H7.
       solveSignature1.
       checkPermutationCases H7.
        BFocus i0 F0 ((i,F)::x0).
        rewrite H10...
      apply H...
      eapply exchangeCCN. 
      2:{ exact H8. }
      rewrite H9. rewrite H7...
      - TFocus F0. 
    - LLExists t.
    - inversion H4...
    - apply InvSubExpPhase in H5...
      checkPermutationCases H5.
      -- rewrite H5 in H10.
         assert(False).
         apply locAlone in H4.
         apply H4... left. 
         inversion H10...
         contradiction. 
      -- checkPermutationCases H5.
         rewrite H5 in H11.
         assert(False).
         apply locAlone in H4.
         apply H4... left.
         inversion H11...
         contradiction.         
         checkPermutationCases H12.
         { (* m4 i = true *)
          (* colocar esse caso *) 
          createWorld.
          eapply GenK4Rel with (C4:=(i,F)::x4) (CK:=x0) (CN:=x3)...    
          rewrite H12 in H6;auto.
          rewrite H12 in H10;auto.
          
          rewrite H5 in H9.
          solveSE.
          rewrite <- H15.
          rewrite <- H14...
          rewrite H12 in H7... 
               eapply HeightGeqCEx.
               2:{ exact H13. }
               rewrite H12...
               rewrite H12...   } 
          createWorld.     
        eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=x3)...
       rewrite H5 in H9. 
       solveSE.
             rewrite <- H15...
             rewrite H14...
             rewrite H12...
   - apply InvSubExpPhase in H4...
   2:{ solveSignature1. }
      checkPermutationCases H4.
      -- rewrite H4 in H6.
         inversion H6...
         solveSignature1.
      -- checkPermutationCases H4.
         rewrite H4 in H11.
         assert(i0 <> loc).
         solveSignature1.
         inversion H11...
         solveSignature1. 
         checkPermutationCases H12.
         { (* m4 i = true *)
          assert(i0 <> loc).
         solveSignature1.
         
           createWorld i0.  
          eapply GenK4Rel with (C4:=(i,F)::x4) (CK:=x0) (CN:=x3)...
          rewrite H12 in H6...
          rewrite H12 in H10...
          rewrite H4 in H9...  solveSE.
          rewrite <- H15.
          rewrite <- H14...
          rewrite H12 in H7... 
               eapply HeightGeqCEx.
               2:{ exact H13. }
               rewrite H12... rewrite H12...  }
         assert(i0 <> loc).
         solveSignature1.
         
           createWorld i0.  
        eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=x3)...
       rewrite H4 in H9...
       solveSE.
             rewrite <- H15...
             rewrite H14...
             rewrite H12...
    Qed.
 
  
   Lemma ContractionL : forall n B C L X, 
   SetU C -> SetT C -> seqN theory n (Loc C++C++B) L X -> 
   seqN theory n (C++B) L X.
  Proof with sauto.
    intros.
    revert dependent B.
    revert dependent X.
    revert dependent L.
    revert dependent n.
    induction C;intros...
    simpl in H1... 
    destruct a as [b F].
   eapply exchangeCCN with (CC:=(b, F) :: C ++ B)...
   apply ContractionLoc...
   solveSE.
   solveSE.
   eapply exchangeCCN with (CC:=C ++ ([(loc, F)] ++ [(b, F)] ++ B))...
   apply IHC...
   solveSE.
   solveSE.
    eapply exchangeCCN.
    2:{ exact H1. }
    simpl... 
  Qed.
  
  Lemma ContractionL' : forall B C L X, 
   SetU C -> SetT C -> seq theory (Loc C++C++B) L X -> 
   seq theory (C++B) L X.
  Proof with sauto.
    intros.
    apply seqtoSeqN in H1.
    destruct H1.
    eapply seqNtoSeq with (n:=x).
    apply ContractionL...
  Qed.

  
  Lemma Loc_Unb : forall n B C L X, 
   SetU C -> SetT C -> seqN theory n (Loc C++B) L X -> 
   seqN theory n (C++B) L X.
  Proof with subst;auto.
    intros.
    apply  ContractionL...
    eapply exchangeCCN with (CC:=(Loc C++B) ++ C)...
    perm. 
    apply weakeningGenN_rev...
  Qed.  

Lemma Loc_Unb' : forall  B C L X, 
   SetU C -> SetT C -> seq theory (Loc C++B) L X -> 
   seq theory (C++B) L X.
  Proof with subst;auto.
    intros.
    apply  ContractionL'...
    eapply exchangeCC with (CC:=(Loc C++B) ++ C)...
    perm. 
    apply weakeningGen_rev...
  Qed.  

 Lemma ContractionLocK4 : forall n a C B L D X, a <> loc -> 
   SetU C -> SetT C ->  tri_bangK4 theory n D a (Loc C++B) L (UP X) -> 
   tri_bangK4 theory n D a (C++B) L (UP X).
  Proof with sauto;try solveLL.
  intros.
  apply InvSubExpPhase in H2...
  apply GenK4Rel with (C4:= x) (CK:= x0) (CN:=x1)...
  eapply exchangeCCN with (CC:=C++(B ++ PlusT x ++ Loc (getU x0)))...
  
  apply Loc_Unb...
  eapply exchangeCCN with (CC:=((Loc C ++ B) ++
         PlusT x ++ Loc (getU x0)))...
 Qed. 
 
 Lemma ContractionLocK4' : forall a C B L D X, a <> loc -> 
   SetU C -> SetT C ->  tri_bangK4' theory  D a (Loc C++B) L (UP X) -> 
   tri_bangK4' theory D a (C++B) L (UP X).
  Proof with sauto;try solveLL.
  intros.
  apply InvSubExpPhase' in H2...
  apply GenK4Rel' with (C4:= x) (CK:= x0) (CN:=x1)...
  eapply exchangeCC with (CC:=C++(B ++ PlusT x ++ Loc (getU x0)))...
  
  apply Loc_Unb'...
  eapply exchangeCC with (CC:=((Loc C ++ B) ++
         PlusT x ++ Loc (getU x0)))...
 Qed. 
 
 Lemma Derivation1 D M F : 
 seq theory D M (DW F) -> seq theory D M (UP [F]).
 Proof with sauto.
 intros.
 destruct(PositiveOrNegative F).
 LLStore...
 LFocus F.  
 inversion H0;inversion H...
Qed. 
  
  Lemma InvBangTN i j B P : u i = true -> mt i = true ->
          seqN theory  j B [] (DW (Bang i P) ) -> seqN theory (j-1) B [] (UP [P]).
  Proof with sauto.
  intros Hu Hm Hj.
  inversion Hj...
  inversion H0.
  eapply InvSubExpPhaseU in H4;auto. 
  destruct H4 as [C4 H4].
  destruct H4 as [CK H4].
  destruct H4 as [CN H4]...
  apply (exchangeCCN (symmetry H))...
  rewrite app_assoc. 
  apply weakeningGenN_rev;auto.
  rewrite Permutation_app_comm.
  apply ContractionL... 
  eapply (SetTKClosure _ _ _ mtClosure Hm)...
  eapply exchangeCCN with (CC:=(C4 ++ Loc CK) ++ CK)...
  apply weakeningGenN_rev;auto.
  rewrite SetTPlusT in H11...
  eapply @HeightGeq with (n:=n - length (C4 ++ CK) - 1)...
   eapply (SetTKClosure _ _ _ mtClosure Hm)... 
 Qed. 
 
  Lemma InvBangT i j B P : u i = true -> mt i = true ->
          seqN theory j B [] (DW (Bang i P)) -> seq theory B [] (UP [P]).
  Proof with sauto.
  intros Hu Hm Hj.
  apply InvBangTN in Hj...
  apply seqNtoSeq in Hj...
 Qed. 


             
End GeneralResults.

  (** Adequacy relating the system with and without inductive meassures *)
  

  (** Weakening in the linear context when the formula belongs to the theory *)
  Section MoreWeakening.
    Variable theory : oo -> Prop .
    
    Theorem WeakLinearTheoryN : forall n CC LC F X ,
        ~ IsPositiveAtom F ->
        (seqN theory n CC (F::LC) X) -> theory F ->
        seqN theory n CC LC X.
    Proof with sauto.
      induction n;intros;subst.
      + inversion H0...
        contradict H ...
      + inversion H0... 
        - contradict H ...
        - checkPermutationCases H3. 
          LLTensor x N B D.
          apply IHn with (F:=F)...
          apply (exchangeLCN H3)...
          LLTensor M x B D.
          apply IHn with (F:=F)...
          apply (exchangeLCN H3)...
        - LLPlusL.
          apply IHn with (F:=F)...
        - LLPlusR. 
          apply IHn with (F:=F)...
        - LLRelease.
          apply IHn with (F:=F)...
        - LLBot.
          apply IHn with (F:=F)...
        - LLPar. 
          apply IHn with (F:=F)...
        - LLWith. 
          apply IHn with (F:=F)...
          apply IHn with (F:=F)...
        - LLStoreC.
          apply IHn with (F:=F)...
        - LLStore.
          apply IHn with (F:=F)...
          eapply (exchangeLCN (perm_swap F F0 LC))...
        - checkPermutationCases H4. 
          TFocus F.
          rewrite <- H7... 
          LFocus F0 x.
          apply IHn with (F:=F)...
          rewrite <- H6...
        - UFocus i F0. 
          apply IHn with (F:=F)...
        - BFocus i F0 B'. 
          apply IHn with (F:=F)...
        - TFocus F0. 
          apply IHn with (F:=F)...
        - LLExists t.
          apply IHn with (F:=F)...
        - LLForall. 
          apply IHn with (F:=F)...
 Qed.         
     
  Theorem WeakLinearTheory : forall CC LC F X,
        ~ IsPositiveAtom F ->
        (seq theory CC (F::LC) X) -> theory F -> seq theory CC LC X.
      intros.
      apply seqtoSeqN in H0.
      destruct H0.
      apply WeakLinearTheoryN in H0;auto.
      apply seqNtoSeq in H0;auto.
  Qed.    
 
 Lemma WeakTheory
     : forall (CC : list TypedFormula)
         (LC : multiset oo) (X : Arrow) (th th' : oo -> Prop),
       (forall F : oo, th F -> th' F) ->
       seq th CC LC X -> seq th' CC LC X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0...
  eapply @WeakTheoryN with (th':=th') in H0...
  apply seqNtoSeq in H0...
 Qed.

  End MoreWeakening.
End FLLBasicTheory.
