(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export FLL.Misc.Utils. 
Require Export FLL.Misc.Permutations. 
Require Export FLL.SL.FLLTacticsPre.
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
       eapply @tri_copyK4 with (b:=b) (F:=F) (B':=B')...
       eapply H with (th:=th)...
       eapply @tri_copyUK with (b:=b) (F:=F) (B':=B')...
       eapply H with (th:=th)...
       eapply @tri_copyLK with (b:=b) (F:=F) (B':=B')...
       eapply H with (th:=th)...
       eapply tri_exp...
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
        tensor M N B D. 
        1-8: eauto.
        eapply H;eauto using Permutation_app_tail.

        generalize (Remove_Permutation_Ex2 H4 H0);intros.
        destruct H2 as [M' [H2 H2']].
        decide1 F M'...
        apply H with (LC' := M') (LC:= L')...
        
        all:eauto.
     Qed.

  Theorem exchangeLC LC : forall CC LC'  (X: Arrow),
        Permutation LC LC' ->
        ( |-f- CC ; LC ; X) -> |-f- CC ; LC' ; X.
    Proof with sauto;solveLL.
    intros.
    revert dependent LC'.
    induction H0;intros...
    * tensor M N B D.
    * destruct(Remove_Permutation_Ex2 H0 H2)... 
      decide1 F x. 
    * decide2u i F.
    * decide2l i F.
    * decide3 F.
    * existential t.
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
  * generalize (Remove_Permutation_Ex2 H1 Hp);intros.
    destruct H2 as [x [H2 H2']].
    copyK4 b F x...
  * generalize (Remove_Permutation_Ex2 H2 Hp);intros.
    destruct H3 as [x [H3 H3']].
    copyUK b F x...
  * generalize (Remove_Permutation_Ex2 H2 Hp);intros.
    destruct H3 as [x [H3 H3']].
    copyLK b F x...    
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
  * generalize (Remove_Permutation_Ex2 H1 Hp);intros.
    destruct H2 as [x [H2 H2']].
    copyK4 b F x... 
  * generalize (Remove_Permutation_Ex2 H2 Hp);intros.
    destruct H3 as [x [H3 H3']].
    copyUK b F x... 
  * generalize (Remove_Permutation_Ex2 H2 Hp);intros.
    destruct H3 as [x [H3 H3']].
    copyLK b F x... 
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
    tensor M N B D0...
    rewrite <- H0...
    rewrite <- H0...
    rewrite <- H0...
    generalize (Remove_Permutation_Ex2 H6 H0);intros.
    CleanContext.
    decide2l i F x...
    eapply H with (CC:=B')...
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
  tensor M N B D. 
  eauto using Permutation_in. 
  eauto using Permutation_in. 
  generalize (Remove_Permutation_Ex2 H2 Hp);intros.
  CleanContext.     
  decide2l i F x...
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
   
  (** However, we can generalize the exponential phase in order to 
     avoid mutual induction *)  
  
 Theorem GenK4 n a B L O D C4 CK CN : 
  a <> loc -> SetK4 a C4 -> SetK a CK -> Permutation B (C4++CK++CN) ->
  tri_bangK4 theory  (n - length (C4 ++ CK)) CN a (D++PlusT C4++Loc (getU CK)) O (> (L ++ second (getL CK))) ->
    tri_bangK4 theory  n B a D O (> L).
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
      - apply (exchangeCCNK4 (symmetry H2))... 
      - destruct n.
        inversion H3. 
         destruct a0 as [b F].
         destruct(uDec b).
       
        + apply (exchangeCCNK4 (symmetry H2))...
           copyUK b F (CK++CN).   
          eapply IHCK with (CN:=CN)... 
          solveSignature.
          rewrite app_assoc_reverse...
        + apply (exchangeCCNK4 (symmetry H2))...
          copyLK b F (CK++CN).
          eapply IHCK with (CN:=CN);try SLSolve...
          eapply exchangeCCNKK4 .
          2:{ simpl in H3. rewrite app_assoc_reverse. exact H3. }
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
        inversion H3. 
        apply (exchangeCCNK4 (symmetry H2))...
        destruct a0 as [b F].
        copyK4 b F (C4++CN).
        eapply IHC4 with (CN:=CN) (CK:=[]);try SLSolve...
        rewrite app_assoc_reverse...
      - simpl in H3...
        destruct n.
        inversion H3. 
        apply (exchangeCCNK4 (symmetry H2))...
        destruct a0 as [b0 F0].
        destruct a1 as [b1 F1]...
        copyK4 b0 F0 (C4++((b1, F1) :: CK) ++ CN). 
        eapply IHC4 with (CN:= CN) (CK:=(b1, F1)::CK); try solve [SLSolve]...
        rewrite app_assoc_reverse...
 Qed.
    
   
Theorem tri_exp_pred n a D O L CN: n >= 1 -> SetU CN ->
   n - 1 |-F- D; O; (> L) ->  tri_bangK4 theory n CN a D O (> L).
 Proof with simplifier;auto.
    destruct n;intros...
    inversion H.
    finishExp. 
 Qed.

(* Theorem tri_exp_pred_inv n a D O L :
   tri_bangK4 theory n [] a D O (> L) -> n |-F- D; O; (> L).
 Proof with sauto.
 intros.
 inversion H...
 apply Remove_In in H3. inversion H3.
 apply Remove_In in H4. inversion H4.
 apply Remove_In in H4. inversion H4.
Abort.
*)

Theorem tri_exp_pred_inv' a D O L :
   tri_bangK4' theory [] a D O (> L) ->  |-f- D; O; (> L).
 Proof with sauto.
 intros.
 inversion H...
 apply Remove_In in H3. inversion H3.
 apply Remove_In in H4. inversion H4.
 apply Remove_In in H4. inversion H4.
Qed. 

(* GenK4Rel *)
 Theorem GenK4Rel n a B D O L CK C4 CN : 
  a <> loc -> SetK4 a C4 -> SetK a CK ->  SetU CN ->
     Permutation B (C4++CK++CN) ->
    n >= length (C4 ++ CK) + 1 -> 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc (getU CK) ; O ;(> L ++ second (getL CK) ) -> 
    tri_bangK4 theory  n B a D O (> L). 
Proof with subst;auto.
    intros.
    eapply GenK4 with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp_pred...
    lia.
 Qed.

 Theorem GenK4RelU n a B D O L CK C4 CN : 
     a <> loc -> SetK4 a C4 -> SetK a CK ->  SetU CN ->
     Permutation B (C4++CK++CN) ->  SetU C4 -> SetU CK ->
    n >= length (C4 ++ CK) + 1 -> 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT C4 ++ Loc (getU CK) ; O ;(> L ) -> 
    tri_bangK4 theory  n B a D O (> L). 
Proof with sauto.
    intros.
    eapply GenK4 with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp_pred...
    lia.
    rewrite SetU_then_empty;simpl... 
 Qed.
   
  Lemma InvSubExpPhase n a B L D O: 
   a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ n >= length (C4++CK) + 1  /\
        SetK4 a C4 /\ SetK a CK /\ SetU CN  /\  
    n - length (C4++CK) - 1 |-F- (D++PlusT C4 ++ Loc (getU CK)) ; O ;(> L++ second (getL CK) ).
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
        CleanContext.
        apply Remove_Permute in H6...
        
        eexists ([(b, F)] ++ x).
        eexists x0.
        eexists x1. 
        split;[| 
        split;[simpl; lia | 
        split;[simpl; SLSolve | 
        split;[SLSolve |
        split]]]]...
        rewrite H6.
        rewrite <- app_assoc. 
        simpl.
        apply Permutation_cons;auto.
        eapply exchangeCCN.
        2:{ exact H12. }
        simpl. perm.
      - eapply H in H12...
        clear H.
        apply Remove_Permute in H7...
        
        eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1. 
        assert( Permutation (x ++ [(b, F)] ++ x0) ((b, F) :: x ++  x0)) by perm.
      
        split;[| 
        split;[| 
        split;[SLSolve | 
        split;[simpl;SLSolve |
        split]]]]...
        rewrite H7.
        rewrite H3. perm.
        simpl. 
        rewrite H.
        simpl; lia.
        rewrite H.
        CleanContext.
        eapply exchangeCCN.
        2:{  exact H13. }
        CleanContext.
   - eapply H in H12...
        clear H.
        apply Remove_Permute in H7...
        
        eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1. 
        assert( Permutation (x ++ [(b, F)] ++ x0) ((b, F) :: x ++  x0)) by perm.
      
        split;[| 
        split;[| 
        split;[SLSolve | 
        split;[simpl;SLSolve |
        split]]]]...
        rewrite H7.
        rewrite H3. perm.
        simpl. 
        rewrite H.
        simpl; lia.
        rewrite H.
        CleanContext.
        eapply exchangeCCN.
        2:{ rewrite (app_assoc_reverse L) in H13. exact H13. }
        CleanContext.
   
      - 
        eexists [].
        eexists [].
        eexists B;CleanContext...
    Qed.  
      
 Lemma InvSubExpPhaseLoc n B L D O: 
   tri_bangK4 theory n B loc D O (> L) ->
   exists CK CN, Permutation B ((Loc (getU CK))++CN) /\ n >= length CK + 1  /\
        SetU CN  /\ 
    n - length (CK) - 1 |-F- (D++Loc (getU CK)) ; O ;(> L).
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
        clear H.
        CleanContext.
        apply Remove_Permute in H6...
        eexists ([(loc, F)] ++ x).
        eexists x0.
        split;auto. 
        rewrite H6.
        rewrite H2.
        CleanContext.
        split;auto.
        simpl. lia.
        split;auto.
        CleanContext.
        eapply exchangeCCN.
        2:{ exact H10. }
        simpl. perm.
      - assert(b = loc).
        apply locAlone'...
        subst.
        solveSubExp.
      - exists []. 
        exists B.
        CleanContext.
      Qed.  

 Lemma InvSubExpPhaseU n a B D O L: 
  u a =  true -> a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 a C4 /\ SetK a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT (getU C4) ++ Loc (getU CK) ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1;auto.
    CleanContext.
      assert(SetU x0). 
    { eapply SetUKClosure with (i:=a);auto. }
     assert(SetU x). 
    { eapply SetUK4Closure with (i:=a);auto. } 
    rewrite (SetU_then_empty H1) in H8... 
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H8. 
    CleanContext. SLSolve.
 Qed.

Lemma InvSubExpPhaseSU n a B D O L: 
  SetU B -> a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 a C4 /\ SetK a CK /\ n >= length (C4++CK) + 1 /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
    n - length (C4 ++ CK) - 1 |-F- D++PlusT (getU C4) ++ Loc (getU CK) ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1;auto.
    CleanContext.
      assert(SetU (x ++ x0 ++ x1)). 
    { rewrite <- H2... }
      assert(SetU (x0 ++ x1)) by SLSolve. 
     assert(SetU x) by SLSolve.
     assert(SetU x1) by SLSolve.
     assert(SetU x0) by SLSolve.
    eexists x.
    eexists x0.
    eexists x1.
    CleanContext. SLSolve. 
 Qed.

  Lemma InvSubExpPhaseK4 n a B D O L: 
  m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ n >= length C4 + 1 /\  SetU CN /\ 
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase in H1;auto.
    CleanContext.
     assert( x0 = []).
    { eapply @SetKK4_then_empty' with (i:=a)...  }
    rewrite H1 in *.
    CleanContext.
    simpl in H8.
    exists x.
    exists x1.
    CleanContext.
   Qed.  


  Lemma InvSubExpPhaseUK4 n a B D O L: 
  u a = true -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ 
    n - length C4 - 1 |-F- D++PlusT C4 ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4 in H2;auto.
    CleanContext.
    exists x.
    exists x0.
    CleanContext.
     eapply SetUK4Closure with (i:=a);auto.
   Qed.
   
  Lemma InvSubExpPhaseSUK4 n a B D O L: 
  SetU B -> m4 a =  true -> a <> loc -> tri_bangK4 theory n B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ n >= length C4 + 1 /\  SetU CN /\  SetU C4 /\ 
    n - length C4 - 1 |-F- D++PlusT (getU C4) ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4 in H2;auto.
    CleanContext.
      assert(SetU (x ++ x0)). 
    { rewrite <- H3... }
    exists x.
    exists x0.
    CleanContext.
    SLSolve.
    eapply exchangeCCN.
    2:{ exact H8. }
    rewrite setUtoGetU...
    SLSolve.
   Qed. 
   
     

 (** Same results for the system without height *)
 Theorem GenK4' a B L O D C4 CK CN : 
  a <> loc -> SetK4 a C4 -> SetK a CK -> Permutation B (C4++CK++CN) ->
  tri_bangK4' theory  CN a (D++PlusT C4++ Loc (getU CK)) O (> L ++ second (getL CK)) ->
    tri_bangK4' theory  B a D O (> L).
  Proof with sauto.
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
      revert dependent CK.
   
     induction C4;intros;CleanContext.
    * 
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
    induction CK;intros;CleanContext.
    simpl in H3.
     symmetry in H2.
      apply (exchangeCCK4 H2)...

     symmetry in H2.
     apply (exchangeCCK4 H2).
     destruct a0 as [b F].
     destruct(uDec b);CleanContext.
        + copyUK b F (CK++CN).
          eapply IHCK with (CN:=CN);try SLSolve...
          rewrite app_assoc_reverse...
        + copyLK b F (CK++CN).
          eapply IHCK with (CN:=CN);try SLSolve...
          simpl in H3. rewrite app_assoc_reverse. exact H3.
     *
    revert dependent L.
    revert dependent D.
    revert dependent O.
    revert dependent B.
     revert dependent CN.
    induction CK;intros;CleanContext.
    
    symmetry in H2.
    apply (exchangeCCK4 H2)...
    destruct a0 as [b F].
    eapply @tri_copyK4' with (b:=b) (F:=F) (B':= C4++CN);try SLSolve...
    eapply IHC4 with (CN:=CN) (CK:=[]);CleanContext;try SLSolve...
    simpl in H3. 
    rewrite app_assoc_reverse.
    eapply exchangeCCKK4.
     2:{ CleanContext. exact H3. }
     perm. 

     symmetry in H2.
      apply (exchangeCCK4 H2)...

     destruct a0 as [b0 F0];
         destruct a1 as [b1 F1].

     eapply @tri_copyK4' with (b:=b0) (F:=F0) (B':= C4++((b1, F1) :: CK) ++ CN);CleanContext;try solve [SLSolve]...
     eapply IHC4 with (CN:= CN) (CK:=(b1, F1)::CK);try solve[SLSolve]...
     eapply exchangeCCKK4.
     2:{ exact H3. }
     simpl. perm.
    Qed.
    
 Theorem GenK4Rel' a B D O L CK C4 CN : 
  a <> loc -> SetK4 a C4 -> SetK a CK -> SetU CN  -> 
     Permutation B (C4++CK++CN) ->
    |-f- D++PlusT C4 ++ Loc (getU CK) ; O ;(> L ++ second (getL CK) ) ->
    tri_bangK4' theory B a D O (> L). 
    Proof with subst;auto.
    intros.
    eapply GenK4' with (C4:=C4) (CK:=CK) (CN:= CN)...
    eapply tri_exp'...
  Qed.
  
 Theorem GenK4RelU' n a B D O L CK C4 CN : 
     a <> loc -> SetK4 a C4 -> SetK a CK -> SetU CN -> 
     Permutation B (C4++CK++CN) ->  SetU C4 -> SetU CK ->
    n >= length (C4 ++ CK) + 1 -> 
    |-f- D++PlusT C4 ++ Loc (getU CK) ; O ;(> L ) -> 
    tri_bangK4' theory B a D O (> L). 
Proof with sauto.
    intros.
    eapply GenK4' with (C4:=C4) (CK:=CK) (CN:= CN)... 
    eapply tri_exp'...
    rewrite SetU_then_empty;simpl... 
 Qed.

  Lemma InvSubExpPhase' a B L D O: 
   a <> loc -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\
        SetK4 a C4 /\ SetK a CK /\ SetU CN /\  
     |-f- (D++PlusT C4 ++ Loc (getU CK)) ; O ;(> L++ second (getL CK) ).
    Proof with sauto.
    intros.
    dependent induction H0...
                
    edestruct IHtri_bangK4'...
     eexists ([(b, F)] ++ x).
        eexists x0.
        eexists x1. 
    CleanContext.
    apply Remove_Permute in H1.
    rewrite H1. rewrite H5. perm.
    exact nil. 
    eapply exchangeCC. 
    2:{ exact H10. } perm. 
     edestruct IHtri_bangK4'...
     eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1. 
    CleanContext.
    apply Remove_Permute in H2.
    rewrite H2. rewrite H6. perm.
    exact nil. 
   eapply exchangeCC. 
    2:{ exact H11. } perm. 
    
    edestruct IHtri_bangK4'...
     eexists x.
        eexists ([(b, F)] ++ x0).
        eexists x1. 
    CleanContext.
    apply Remove_Permute in H2.
    rewrite H2. rewrite H6. perm.
    exact nil. 
    rewrite (app_assoc_reverse L) in H11.
    exact H11.
    do 2 exists [].
    exists B.
    CleanContext...
    Qed.
 
  Lemma InvSubExpPhaseU' a B D O L: 
  u a =  true -> a <> loc -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 a C4 /\ SetK a CK /\  SetU C4 /\ SetU CK  /\ SetU CN /\ 
   |-f- D++PlusT (getU C4) ++ Loc (getU CK) ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1;auto.
    CleanContext.
      assert(SetU x0). 
    { eapply SetUKClosure with (i:=a);auto. }
     assert(SetU x). 
    { eapply SetUK4Closure with (i:=a);auto. } 
    rewrite (SetU_then_empty H1) in H7... 
    eexists x.
    eexists x0.
    eexists x1.
    simpl in H7. 
    CleanContext. SLSolve.
 Qed.


 Lemma InvSubExpPhaseSU' a B D O L: 
  SetU B -> a <> loc -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CK CN, Permutation B (C4++CK++CN) /\ 
        SetK4 a C4 /\ SetK a CK /\  SetU C4 /\ SetU CK  /\ SetU CN /\  
   |-f- D++PlusT (getU C4) ++ Loc (getU CK) ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1;auto.
    CleanContext.
    
      assert(SetU (x ++ x0 ++ x1)). 
    { rewrite <- H2... } 
      assert(SetU x). 
      SLSolve. 
      assert(SetU (x0++x1)). 
      SLSolve. 
      assert(SetU x0). 
      SLSolve. 
      assert(SetU x1). 
      SLSolve. 
    rewrite (SetU_then_empty H9) in H7...
    assert(Permutation (PlusT x) (PlusT (getU x))).
    rewrite (cxtDestruct x). 
    CleanContext.
    assert(|-f- D ++ PlusT (getU x) ++ Loc (getU x0); O; (> L))...
    CleanContext. SLSolve.
    firstorder.
 Qed.

  Lemma InvSubExpPhaseK4'  a B D O L: 
  m4 a =  true -> a <> loc -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ SetU CN /\ 
    |-f- D++PlusT C4 ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhase' in H1;auto.
    CleanContext.
     assert( x0 = []).
    { eapply @SetKK4_then_empty' with (i:=a)...  }
    rewrite H1 in *.
    CleanContext.
    simpl in H7.
    exists x.
    exists x1.
    CleanContext.
   Qed.  

 Lemma InvSubExpPhaseUK4'  a B D O L: 
 u a = true -> m4 a =  true -> a <> loc -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ SetU CN /\  SetU C4 /\ 
    |-f- D++PlusT C4 ; O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseK4' in H2;auto.
    CleanContext.
    exists x.
    exists x0.
    CleanContext.
     eapply SetUK4Closure with (i:=a);auto.
   Qed.
  
 Lemma InvSubExpPhaseSUK4' a B D O L: 
  SetU B -> m4 a = true -> tri_bangK4' theory B a D O (> L) ->
   exists C4 CN, Permutation B (C4++CN) /\ 
        SetK4 a C4 /\ SetU C4 /\ SetU CN /\ 
   |-f- D++PlusT (getU C4); O ;(> L).
 Proof with sauto.
    intros.
    eapply InvSubExpPhaseSU' in H1;auto.
    CleanContext.
     assert( x0 = []).
    { eapply @SetKK4_then_empty' with (i:=a)...  }
    rewrite H1 in *.
    CleanContext.
    simpl in H9.
    exists x.
    exists x1.
    CleanContext. SLSolve.
    intro...
    rewrite loc4 in H0...
  Qed.
   
      
 Theorem BangUnb n i BD M P: 
    u i = true -> n |-F- BD; M ; DW (i ! P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0...
 inversion H2.
 apply InvSubExpPhaseU in H7...
 rewrite H2.
 SLSolve...
 Qed.
    
 Theorem BangUnb' i BD M P: 
    u i = true -> |-f- BD; M ; DW (i ! P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0...
 inversion H2.
 apply InvSubExpPhaseU' in H6...
 rewrite H2.
 SLSolve...
 Qed.
 
          
 (* Soundness using mutuality *)
 Lemma seqNtoSeq_mutual : forall n a B D O L (X:Arrow),
    (tri_bangK4 theory n B a D O (> L )  -> tri_bangK4' theory B a D O (> L )) /\
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
           eapply @tri_bangD' with (i:=i)...
           eapply H...
           firstorder.
Qed.       
                 
    
(* Soundness using inversion lemma of bang *)   
Lemma seqNtoSeq : forall n B C X,
    seqN theory n B C X -> seq theory B C X.
     Proof with subst;eauto. 
      induction n using strongind;intros;eauto.
      + inversion H...
      + inversion H0...  
        apply InvSubExpPhase in H3...
        CleanContext.
        apply exchangeCC with (CC:=x ++ x0 ++ x1).
        rewrite H3. perm.
        createWorld.
        
        eapply GenK4'...
        finishExp.
        eapply H with (m:=n - length (x ++ x0) - 1)... 
        lia.
        eapply InvSubExpPhase in H2...
        CleanContext.
        createWorld i.
        eapply GenK4'...
        SLSolve.
        finishExp.
          
        eapply H with (m:=n - length (x ++ x0) - 1)... 
        lia.
        SLSolve.
  Qed. 
 
 
   Lemma HeightGeq_mutual : forall n a B D O L (X:Arrow),
        (tri_bangK4 theory n B a D O (> L) ->
        forall m, m>=n -> tri_bangK4 theory m B a D O (> L)) /\
        (seqN theory n B O X ->
        forall m, m>=n -> seqN theory m B O X).
    Proof with sauto;solveLL.
    intro.
      induction n;split;intros ...
      + inversion H ...
      + inversion H ...
      + inversion H...
        - inversion H0... 
          eapply @tri_copyK4 with (b:=b) (F:=F) (B':=B')...
          eapply IHn...
        - inversion H0... 
          eapply @tri_copyUK with (b:=b) (F:=F) (B':=B')...
          eapply IHn...
        - inversion H0... 
          eapply @tri_copyLK with (b:=b) (F:=F) (B':=B')...
          eapply IHn...
        - inversion H0... 
          eapply tri_exp...
          eapply IHn...
      + assert(Hp: forall B O (X : Arrow),
         seqN theory n B O X ->
         forall m : nat, m >= n -> seqN theory m B O X).
         intros. apply IHn;auto.
         inversion H;subst; try mgt0. 
         init1. init2 i C. 
         intuition.

         (* tensor *)
         eapply @tri_tensor with (B:=B0) (D:=D);eauto;try eapply IHn;try lia ...
         1-9: intuition;eauto using Hp...
        (* dec *)
        eapply @tri_dec1 with (F:=F);eauto;eapply IHn;try lia...
        eapply @tri_dec2u with (F:=F) (i:=i);eauto;eapply IHn;try lia...
        eapply @tri_dec2l with (F:=F) (i:=i);eauto;eapply IHn;try lia...
        eapply @tri_dec3 with (F:=F);eauto;eapply IHn;try lia...
        (* exists*)
        eapply tri_ex;eauto;eapply IHn;try lia...
        intuition;eauto using Hp...
        intuition;eauto using Hp...
        (* bang *)
        eapply tri_bang;auto;eapply IHn;try lia...
        firstorder.
       eapply @tri_bangD with (i:=i);auto;eapply IHn;try lia...
       exact (UP nil).
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
    (tri_bangK4 theory n CC i D O (> L) ->
    tri_bangK4 theory n (CC) i (D++[F]) O (> L)) /\
    (tri_bangK4 theory n CC i D O (> L) ->
    tri_bangK4 theory n (CC++[F]) i (D) O (> L)) /\    
    (n |-F- CC ; LC ; X -> n |-F- F :: CC ; LC ; X).
   Proof with sauto;solveLL.   
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
         eapply H... } 
       {  
         copyUK b F0 (B'++[F])...
         eapply H... }
       {  
         copyLK b F0 (B'++[F])...
         eapply H... }         
       {  finishExp... SLSolve. }      
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
        tensor M N ((s,o)::B) ((s,o)::D0)...
        CleanContext.
        CleanContext.
        CleanContext.
        eapply exchangeCCN with (CC:=F::(i0,F0)::CC)...
        eauto using HX .
        
        decide2u i0 F0...
        decide2l i0 F0 (F::B')...
        decide3 F0. 
        existential t.
        eapply exchangeCCNK4 with (CC:=CC++[F])...
        eapply H...
        firstorder.
        createWorld i0.
    eapply exchangeCCNK4 with (CC:=CC++[F])...
        eapply H...
        firstorder.
   Qed.     
    
  (**  Weakening using inversion lemma of bang *)
  Theorem weakeningN : forall n CC LC F X ,
      u (fst F) = true -> n |-F- CC ; LC ; X -> n |-F- F :: CC ; LC ; X.
   Proof with sauto;solveLL.
    induction n using strongind;intros.
    * inversion H0...
      init2 i (F::C).
      rewrite <- H3...
    * inversion H1...
      init2 i (F::C).
      rewrite <- H4...
      tensor M N (F::B) (F::D)...
      destruct F as [a F]. 
      simpl in H0. rewrite H0...
      destruct F as [a F]. 
      simpl in H0. rewrite H0...
      destruct F as [a F]. 
      simpl in H0. rewrite H0...
      3:{ decide2u i F0... }
      3:{ decide2l i F0 (F::B')... }
      5:{
      apply InvSubExpPhase in H4... 
      eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=F::x1);auto...
      rewrite H4. perm. }
     5:{
      apply InvSubExpPhase in H3...
      createWorld i.
      eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=F::x1);auto...
      SLSolve.
      rewrite H3. perm. 
      SLSolve. 
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
      apply weakeningN ;auto.
      SLSolve.
      apply IHCC'. SLSolve.
    Qed.

    Theorem weakeningGenN_rev CC LC CC' X n:
      n |-F- CC ; LC ; X -> SetU CC' -> n |-F- CC++ CC' ; LC ; X.
    Proof.  
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
    Qed.
  
  
 
   
  Theorem seqtoSeqN : forall D O X, 
        seq theory  D O X -> exists n, (seqN theory n D O X).
  Proof with subst;auto.
  Admitted.
  
  Lemma weakeness_mutual' : forall i CC  D O F L,
    u (fst F)= true ->
    (tri_bangK4' theory CC i D O (> L) ->
    tri_bangK4' theory (CC++[F]) i (D) O (> L)).
   Proof with sauto;solveLL.
   intros.
   revert dependent F.
   induction H0;intros...
   * eapply @tri_copyK4' with (b:=b) (F:=F) (B':=B'++ [F0])... 
   * eapply @tri_copyUK' with (b:=b) (F:=F) (B':=B'++ [F0])... 
   * eapply @tri_copyLK' with (b:=b) (F:=F) (B':=B'++ [F0])... 
   * finishExp. SLSolve.
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
      tensor M N ((s, o)::B) ((s, o)::D). 
      all:CleanContext.
    * solveLL.
      rewrite perm_swap...
    * decide1 F.
    * decide2u i F.
    * decide2l i F (F0::B').
    * decide3 F. 
    * existential t.
    * apply InvSubExpPhase' in H0... 
      apply tri_bang'...
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=F0::x1)...
      rewrite H2... perm.
    * assert(i <> loc).
      intro...
      rewrite locD in H0...
      apply InvSubExpPhase' in H... 
      apply @tri_bangD' with (i:=i)...
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=F::x1)...
      rewrite H3... perm.
 Qed.     
   
    Theorem weakeningGen CC LC CC' X:
    SetU CC' -> |-f- CC ; LC ; X -> |-f- CC' ++ CC ; LC ; X.
    Proof with auto;try SLSolve. 
      induction CC';simpl;intros;auto.
      apply weakening...
      apply IHCC'...
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
     * init1.
     * init2 i C.
     * apply tri_one'.
       rewrite <- H0...
     * tensor M N B D. 
       rewrite <- H3...
       rewrite <- H3...
       rewrite <- H3...
     * decide1 F. 
     * decide2u i F.
       rewrite <- H4... 
     * destruct(Remove_Permutation_Ex2 H2 H4)...
       decide2l i F x.
     * decide3 F.
     * existential t.
     * apply tri_bangL'.
       rewrite <- H1...
       apply IHseq...
     * apply InvSubExpPhase' in H0... 
      apply tri_bang'...
      apply GenK4Rel' with (C4:=x) (CK:=x0) (CN:=x1)...
     * assert(i <> loc).
      intro...
      rewrite locD in H0...
      apply InvSubExpPhase' in H... 
      apply @tri_bangD' with (i:=i)...
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
  n |-F- B ; L ; (>> i ! P) -> 
  n |-F- B ; L ; (>> a ! P).
  Proof with CleanContext.
    intros.
    inversion H0...
    assert(a=loc).
    apply locAlone';auto.
    subst;auto.
    apply InvSubExpPhase in H7...
    assert(SetK a x0).
    eapply SetKTrans. 
    exact H5. 
    assumption. 
    assert(SetK4 a x).
    eapply SetK4Trans. 
    exact H3. 
    assumption. 
    
    assert(a <> loc).
    intro... 
    SLSolve.
    apply tri_bang...
     
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

 Theorem InitPosNegN : forall Gamma A, SetU Gamma ->
        seqN theory 2 Gamma [atom A ; perp A ] (UP []).
      intros.
      eapply tri_dec1 with (F:= (perp A )).
      intro Hp;inversion Hp.
      repeat constructor.
      apply tri_init1;auto.
    Qed.
    
    Theorem InitPosNegDwN : forall Gamma A, SetU Gamma ->
        seqN theory 4 Gamma [perp A ] (DW (atom A)).
      intros.
      apply tri_rel.
      constructor.
      apply tri_store.
      intro Hp. inversion Hp.
      simpl. apply InitPosNegN;auto.
    Qed.

    Theorem InitPosNeg : forall Gamma A,
    SetU Gamma -> seq theory Gamma [atom A ; perp A ] (UP []).
      intros.
      decide1 (perp A). 
    Qed. 

    Theorem InitPosNeg' : forall Gamma A,
     SetU Gamma -> seq theory Gamma [perp A ; atom A ] (UP []).
      intros.
      decide1 (perp A). 
    Qed.
    
  End AdmissibleRules.

  (** Some simple invertibility lemmas *)
  Section Invertibility.
    Variable theory : oo -> Prop. (* Theory Definition *)


 Theorem FocusAtomN: forall n Gamma Delta A,
        (seqN theory n Gamma Delta (>> ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma /\ mt i = true).
    Proof with subst;auto.
      intros.
      inversion H ...
      2:{ inversion H1. }
      right.
      exists i;exists C;firstorder.
    Qed.


  Theorem FocusAtom: forall Gamma Delta A,
        (seq theory Gamma Delta (>> ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma /\ mt i = true).
  Proof with subst;auto.
      intros.
       inversion H ...
      2:{ inversion H1. }
      right.
      exists i;exists C;firstorder.
    Qed. 
 
  Theorem FocusAtomTensorN: forall n Gamma Delta A F,
        (seqN theory n Gamma Delta (>> ((perp A) ** F))) -> 
       In (atom A) Delta \/  
        (exists i C D B, SetU C /\ seqN theory (n-1) D Delta (>> F) /\ seqN theory (n-1) B [] (>> (perp A)) /\
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
        rewrite H2...
        init2 x x0.
      - inversion H1.
     Qed.   
    
   
    Theorem FocusAtomTensorInvN: forall n  A F,
        (seqN theory n []  [atom A] (>> ((perp A) ** F))) ->
        (seqN theory (sub n  1 ) [] [] (>> (F))).
    Proof with sauto.
      intros.
      inversion H;simpl;rewrite Nat.sub_0_r...
      apply FocusAtomN in H9...
      * simpl in *. 
       rewrite (cxtDestruct B) in H2...
       rewrite H3 in H2.
       rewrite H0 in H2...
      *  simpl in *. 
       rewrite (cxtDestruct D) in H10...
       rewrite H4 in H10.
       rewrite H1 in H10...
      * inversion H1.  
    Qed.   
    
    
    Theorem FocusAtomTensorTop: forall A B,
        (seq theory B [atom A] (>> ((perp A) ** top))).
    Proof with sauto.
      intros.
      tensor [atom A] (@nil oo) (getU B) B...
    Qed.  
    
    Theorem FocusTopOplus1: forall F B D,
        (seq theory B D (>> top op F)).
    Proof with sauto.
      intros.
      oplus1.
    Qed.  
    
    Theorem FocusTopOplus2: forall F B D,
        (seq theory B D (>> F op top)).
    Proof with sauto.
      intros.
      oplus2.
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
  Proof.
   intros.
   checkPermutationCases H.
   exists x.
   split;auto.
   apply getLPerm_SetL in H1.
   assert(u (fst F) = false) by SLSolve. 
   sauto.
   Qed.   


  Theorem contractionN  : forall n CC LC F X,
       u (fst F) = true -> seqN theory n (F :: CC) LC X -> In F CC -> seqN theory n CC LC X. 
  Proof with CleanContext;solveLL.
  induction n using strongind;intros. 
  * inversion H0...
    checkPermutationCases H4.
    apply InPermutation in H1...
    rewrite H7 in H2.
    rewrite H1 in H2. SLSolve.
    init2 i x.
   * inversion H1...
    checkPermutationCases H5.
    apply InPermutation in H2.
    destruct H2.
    init2 i x. rewrite H8 in H3.
    rewrite H2 in H3.
    SLSolve.
    init2 i x.
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
 
    tensor M N x0 x...
  
    rewrite H10 in H5.
    simplSignature. 
    apply Permutation_cons_inv in H5;auto.
    rewrite H3 in H6.
    simplSignature. 
    apply Permutation_cons_inv in H6;auto.
    rewrite H10 in H7. rewrite H3 in H7.
    simplSignature;auto.
    
    eapply H with (F:=(s, o))...
    rewrite <- H10...
    assert( Permutation (getU CC) (getU x0)).
    rewrite H10 in H5.
    simplSignature. 
    apply Permutation_cons_inv in H5;auto.
    assert(In (s, o) (getU CC)).
    apply uIngetU...
    rewrite H11 in H12.
    rewrite cxtDestruct.
    apply in_or_app.
    left...
     eapply H with (F:=(s, o))...
    rewrite <- H3...
    assert( Permutation (getU CC) (getU x)).
    rewrite H3 in H6.
    simplSignature. 
    apply Permutation_cons_inv in H6;auto.
    assert(In (s, o) (getU CC)).
    apply uIngetU...
    rewrite H11 in H12.
    rewrite cxtDestruct.
    apply in_or_app.
    left...
    1-7:eauto.
    apply H with (F:=F)...
    1-3: eauto.
      eapply exchangeCCN with (CC:=(i,F0)::F::CC)...
    
    decide2u i F0...
    eapply H with (F:=(i, F0))...
    decide2u i F0...
    eapply H with (F:=F)...
    inversion H7...  
   
     assert(In F l2).
      apply Remove_Permute in H12...
     rewrite H12 in H2.
     inversion H2... 
    decide2l i F0 l2...
    eapply H with (F:=F)...
    
    1-5:eauto.
    -
    apply InPermutation in H2.
    destruct H2.
    apply InvSubExpPhase in H5;auto.
    destruct H5 as [C4 H5].
    destruct H5 as [CK H5].
    destruct H5 as [CN H5]...
    
    checkPermutationCases H3.
    (* F is in x or x0 or x1 *)
      + 
      rewrite H2 in H10.
      checkPermutationCases H10.
      --  apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=CN)...
          apply Forall_cons... 
          rewrite H10 in H5.
          rewrite H5 in H6.
          inversion H6...
          rewrite H10 in H5.
          rewrite H5 in H6.
          inversion H6...
          rewrite H10 in H5.
          rewrite H5 in H6.
          inversion H6...
          inversion H15...
          rewrite H10 in H5.
          rewrite H5 in H7.
          simpl in H7.
          apply lt_S...
          simpl. 
          eapply H with (F:=(plust (fst F), snd F)).
          lia.
          simpl.
          apply plust_keepingu;auto.
          remember (n - length (x0 ++ CK) - 1) as Hh.
          rewrite H10 in HeqHh.
          simpl in HeqHh.
          eapply HeightGeqCEx.
          2:{ exact H11. }
          srewrite H5.
          srewrite H10.
          simpl. perm.
          rewrite H5 in H7.
          rewrite H10 in H7.
          subst. simpl in H7. 
          assert(Hs: n >= (S (length (x1 ++ CK) + 1))).
          apply lt_S...
          rewrite H5.
          rewrite H10.
          
          apply Nat.sub_le_mono_r... 
          firstorder.
      --  checkPermutationCases H10.
          ++
          rewrite H5 in H6.
          rewrite H10 in H8.
          
          inversion H8...
          inversion H6...
          ++
          apply GenK4Rel with (C4:=F::x0) (CK:=CK) (CN:=x2)...
          srewrite H5 in H6...
     
          rewrite H10 in H9.
          SLSolve.
          rewrite H2.
          rewrite <- H12.
          rewrite <- H13. 
          perm.
     
          rewrite H5 in H7.
          simpl in H7...
          simpl. 
          eapply HeightGeqCEx.
          2:{ exact H11. }
          rewrite H5.
          simpl. perm.
          
          rewrite H5. 
          simpl... 
    + rewrite H2 in H10.
      checkPermutationCases H10.
     --  checkPermutationCases H5.
         ++ rewrite H5 in H8.
            rewrite H10 in H6.
            inversion H6...
            inversion H8...
         ++ apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=x2)...
            srewrite H10 in H6...
            srewrite H5 in H9.
            SLSolve.
            rewrite H2.
            rewrite <- H12.
            rewrite <- H13. 
            perm.
            rewrite H10 in H7.
            simpl in H7...
            simpl. 
          eapply HeightGeqCEx.
          2:{ exact H11. }
          rewrite H10.
          simpl. perm.
          
            rewrite H10...
     --  checkPermutationCases H5.
         ++ rewrite <- H13 in H10.
            checkPermutationCases H10.
            {
            assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
            
            apply Permutation_vs_cons_inv in H5;auto.
            CleanContext.
            assert(Permutation (x4 ++ (s,o) :: x5) ((s,o) :: x4 ++ x5)) by perm.
         assert( Permutation (C4 ++ x4 ++ (s,o) :: x5) ((s,o) :: C4 ++ x4 ++ x5)) by perm.
         rewrite H15 in H7.
          rewrite H15 in H11.
            apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN);auto.
            apply Forall_app in H8.
            CleanContext.
            inversion H17...
            SLSolve.
            rewrite H2. 
            rewrite <- H12.
            rewrite <- H14.
            rewrite H3 in H5.
            apply Permutation_cons_inv in H5.
            rewrite H5.
            rewrite H10...
            simpl in H7...
            eapply H with (F:=(loc, o))...
            SLSolve. 
            CleanContext.
            eapply HeightGeqCEx.
            2:{ exact H11. }
            CleanContext.
            simpl...
            apply in_or_app.
            right. 
               rewrite H3 in H5.
            apply Permutation_cons_inv in H5.
            rewrite <- locApp.
            setoid_rewrite <- getUApp.
           
            rewrite H5.
            rewrite H10.
            CleanContext. }
            { 
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
           rewrite H10 in H9.
           SLSolve.
           rewrite H2.
           rewrite <- H12.
           rewrite H5.
           rewrite <- H14. perm. }
      ++ rewrite <- H13 in H10.
         checkPermutationCases H10.
          { 
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x2);auto.
           rewrite H5 in H9.
           SLSolve.
           rewrite H2.
           rewrite <- H12.
           rewrite <- H14.
            rewrite H10. perm. }
         
           { 
           assert(tri_bangK4 theory n ((x++[F])) i [] [] (> [F0])).
           eapply weakeness_mutual with (F:=F)...
           exact nil. firstorder.
           
           apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
             rewrite H5 in H9.
             rewrite H10 in H9.
             inversion H9...
                 SLSolve.
           rewrite <- H12.
           rewrite <- H14...
           eapply exchangeCCNK4. 
           2:{  exact H3. }
           rewrite H2... }
-            
 apply InPermutation in H2.
    destruct H2.
    apply InvSubExpPhase in H4;auto.
    destruct H4 as [C4 H4].
    destruct H4 as [CK H4].
    destruct H4 as [CN H4]...
 
    checkPermutationCases H3.
    (* F is in x or x0 or x1 *)
    + 
      rewrite H2 in H10.
      checkPermutationCases H10.
      --  eapply @tri_bangD with (i:=i)...
          apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=CN)...
          intro...
          solveSignature.
          apply Forall_cons... 
          rewrite H4 in H6.
          inversion H6...
          rewrite H4 in H6.
          inversion H6...
          rewrite H4 in H6.
          rewrite H10 in H6.
          inversion H6...
          inversion H15...
          rewrite H4 in H7.
          rewrite H10 in H7.
          simpl in H7.
          apply lt_S...
          simpl. 
          eapply H with (F:=(plust (fst F), snd F)).
          lia.
          simpl.
          apply plust_keepingu;auto.
          remember (n - length (x0 ++ CK) - 1) as Hh.
          rewrite H10 in HeqHh.
          simpl in HeqHh.
          eapply HeightGeqCEx.
          2:{ exact H11. }
          rewrite H4.
          rewrite H10.
          simpl. perm.
          rewrite H4 in H7.
          rewrite H10 in H7.
          subst. simpl in H7. 
          assert(Hs: n >= (S (length (x1 ++ CK) + 1))).
          apply lt_S...
          rewrite H4.
          rewrite H10.
          
          apply Nat.sub_le_mono_r... 
          firstorder.
      --  checkPermutationCases H10.
          ++
          rewrite H4 in H6.
          rewrite H10 in H8.
          
          inversion H6...
          inversion H8...
          ++
          eapply @tri_bangD with (i:=i)...
          apply GenK4Rel with (C4:=F::x0) (CK:=CK) (CN:=x2)...
          intro...
          solveSignature.
          rewrite H4 in H6...
         
          rewrite H10 in H9.
          SLSolve.
          rewrite H2.
          rewrite <- H12.
          rewrite <- H13. 
          perm.
     
          rewrite H4 in H7.
          simpl in H7...
          simpl. 
          eapply HeightGeqCEx.
          2:{ exact H11. }
          rewrite H4.
          simpl. perm.
          
          rewrite H4. 
          simpl... 
    + rewrite H2 in H10.
      checkPermutationCases H10.
     --  checkPermutationCases H4.
         ++ rewrite H4 in H8.
            rewrite H10 in H6.
            inversion H6...
            inversion H8...
         ++ 
          eapply @tri_bangD with (i:=i)...
          
            apply GenK4Rel with (C4:=F::x1) (CK:=CK) (CN:=x2)...
            
             intro... solveSignature.
            srewrite H10 in H6...
            srewrite H4 in H9.
            SLSolve.
            rewrite H2.
            rewrite <- H12.
            rewrite <- H13. 
            perm.
            rewrite H10 in H7.
            simpl in H7...
            simpl. 
          eapply HeightGeqCEx.
          2:{ exact H11. }
          rewrite H10.
          simpl. perm.
          
            rewrite H10...
     --  checkPermutationCases H4.
         ++ rewrite <- H13 in H10.
            checkPermutationCases H10.
            {
            assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
            
            apply Permutation_vs_cons_inv in H4;auto.
            
            
            CleanContext.
            assert(Permutation (x4 ++ (s, o) :: x5) ((s, o) :: x4 ++ x5)) by perm.
         assert( Permutation (C4 ++ x4 ++ (s, o) :: x5) ((s, o) :: C4 ++ x4 ++ x5)) by perm.
         rewrite H15 in H7.
          rewrite H15 in H11.
           eapply @tri_bangD with (i:=i)...
         
            apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN);auto.
            intro... solveSignature.
            apply Forall_app in H8.
            CleanContext.
            inversion H17...
            SLSolve.
            rewrite H2. 
            rewrite <- H12.
            rewrite <- H14.
            rewrite H3 in H4.
            apply Permutation_cons_inv in H4.
            rewrite H4.
            rewrite H10...
            simpl in H7...
            eapply H with (F:=(loc, o))...
            solveSignature.
            CleanContext. 
            eapply HeightGeqCEx.
            2:{ exact H11. }
            CleanContext.
            simpl...
            apply in_or_app.
            right. 
               rewrite H3 in H4.
            apply Permutation_cons_inv in H4.
            rewrite <- locApp.
            setoid_rewrite <- getUApp.
            rewrite H4.
            rewrite H10.
            CleanContext. }
            {
          eapply @tri_bangD with (i:=i)...
            
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
            intro... solveSignature.
           rewrite H10 in H9.
           SLSolve.
           rewrite H2.
           rewrite <- H12.
           rewrite H4.
           rewrite <- H14. perm. }
      ++ rewrite <- H13 in H10.
         checkPermutationCases H10.
          {
          eapply @tri_bangD with (i:=i)...
          
            apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x2);auto.
            intro... solveSignature. 
           rewrite H4 in H9.
           SLSolve.
           rewrite H2.
           rewrite <- H12.
           rewrite <- H14.
            rewrite H10. perm. }
         
           {
          
           assert(tri_bangK4 theory n ((x++[F])) i [] [] (> [ ])).
           eapply weakeness_mutual with (F:=F)...
           exact nil. exact (UP nil). 
           
           apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
           intro... solveSignature. 
             rewrite H4 in H9.
             rewrite H10 in H9.
             inversion H9...
                 SLSolve.
           rewrite <- H12.
           rewrite <- H14...
            eapply @tri_bangD with (i:=i)...
           eapply exchangeCCNK4. 
           2:{  exact H3. }
           rewrite H2... }
      + intro... solveSignature.      
               
 Qed.
 

 Theorem contractionK4N  : forall n i CC D LC F X, i <> loc -> 
       u (fst F) = true -> tri_bangK4 theory n (F :: CC) i D LC X -> In F CC -> 
       tri_bangK4 theory n CC i D LC X. 
Proof with sauto;solveLL.
  intros. 
  destruct X.
  2:{ inversion H1. }
    apply InvSubExpPhase in H1;auto.
    destruct H1 as [C4 H1].
    destruct H1 as [CK H1].
    destruct H1 as [CN H1]...
    
    checkPermutationCases H3.
  *  
    apply InPermutation in H2.
    CleanContext.
    rewrite H1 in H8.
     checkPermutationCases H8.
    -  
    apply GenK4Rel with (C4:=x) (CK:=CK) (CN:=CN)...
    rewrite H3 in H4.
    SLSolve.
    rewrite H1.
    rewrite <- H10.
    rewrite H8...
    rewrite H3 in H5.
    simpl in H5...
    destruct F;CleanContext. 
    assert(u (fst(plust s,o)) = true).
    apply plust_keepingu;auto.
    eapply contractionN.
    exact H2.
    eapply HeightGeqCEx.
    2:{ exact H9. }
    rewrite H3.
    CleanContext.
      rewrite H3.
    CleanContext.
  
    apply in_or_app.
    right.  
    apply in_or_app.
    left.
    rewrite H8...
   - 
    checkPermutationCases H8.
    rewrite H3 in H4.
    rewrite H8 in H6.
    inversion H4.
    inversion H6...
    apply GenK4Rel with (C4:=C4) (CK:=CK) (CN:=x2)...
    rewrite H8 in H7. SLSolve.
    rewrite H1.
    rewrite <- H10.
    rewrite <- H11.
    rewrite H3...
 *   
     apply InPermutation in H2.
    CleanContext.
    rewrite H1 in H8.
    checkPermutationCases H8.
   -
    checkPermutationCases H3.
    + rewrite H3 in H6.
      rewrite H8 in H4.
      inversion H4...
      inversion H6...
    +  
    apply GenK4Rel with (C4:=F::x1) (CK:= CK) (CN:=x2);auto.
    rewrite H8 in H4...
    rewrite H3 in H7.
    SLSolve.
    rewrite H1.
    rewrite <- H10.
    rewrite <- H11...
    rewrite H8 in H5...
        CleanContext.
    eapply HeightGeqCEx.
    2:{ exact H9. }
    rewrite H8...
    rewrite H8...
   - rewrite H8 in H3.  
     checkPermutationCases H3.
     + checkPermutationCases H11.
       assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
     {  apply Permutation_vs_cons_inv in H3;auto. }
     CleanContext.
     assert(Permutation (x4 ++ (s, o) :: x5) ((s, o) :: x4 ++ x5)) by perm.
     assert( Permutation (C4 ++ x4 ++ (s, o) :: x5) ((s, o) :: C4 ++ x4 ++ x5)) by perm.
     rewrite H2 in *.
     rewrite H13 in *.
     clear H2 H13.
     apply GenK4Rel with (C4:=C4) (CK:= x4 ++ x5) (CN:=CN);auto.
     SLSolve. 
     rewrite H1. 
     rewrite <- H10.
     rewrite <- H12.
     rewrite H11 in H3.
     apply Permutation_cons_inv in H3.
     rewrite H3...
     simpl in H5...
      CleanContext.
    eapply contractionN  with (F:=(loc, o))...
    solveSignature.
    eapply HeightGeqCEx.
    2:{ exact H9. }
    CleanContext.
    CleanContext.
    rewrite <- locApp.
    setoid_rewrite <- getUApp.
    apply Permutation_cons_inv in H3.
    rewrite H3.
    rewrite H11. 
    CleanContext.
    apply in_or_app.
    right.
    apply in_or_app.
    right...
      apply GenK4Rel with (C4:=C4) (CK:= CK) (CN:=x3);auto.
    rewrite H11 in H7.
    SLSolve.  
    rewrite H1. rewrite <- H10. rewrite <- H12. rewrite H3...
   +  
  checkPermutationCases H11.
       assert(exists l' l'' : list (subexp * oo), CK = l' ++ F :: l'').
     {  apply Permutation_vs_cons_inv in H11;auto. }
     CleanContext.
     assert(Permutation (x4 ++ (s, o) :: x5) ((s, o) :: x4 ++ x5)) by perm.
     assert( Permutation (C4 ++ x4 ++ (s, o) :: x5) ((s, o) :: C4 ++ x4 ++ x5)) by perm.
     rewrite H2 in *.
     rewrite H13 in *.
     apply Permutation_cons_inv in H11.
     
     apply GenK4Rel with (C4:=C4) (CK:=(s, o):: x4 ++ x5) (CN:=x2);auto.
     SLSolve.
     rewrite H3 in H7. 
     rewrite H1. 
     rewrite <- H10.
     rewrite <- H12.
     rewrite H11...
     rewrite H13.
     simpl in H5...
      CleanContext.
    eapply HeightGeqCEx.
    2:{ exact H9. }
    CleanContext.
    rewrite H13.
    CleanContext.
    apply GenK4Rel with (C4:=C4) (CK:=CK) (CN:=x2);auto.
    rewrite H3 in H7.
    SLSolve.
    rewrite H1.
    rewrite <- H10.
    rewrite <- H12.
    rewrite H11...
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
Proof with sauto;solveLL. 
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
      SLSolve.
      eapply exchangeCC with (CC':=a :: (L ++ CC)) in H1;[|auto].
      apply contraction in H1;auto.
      SLSolve.
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
      SLSolve.
      eapply exchangeCCK4 with (CC':=a :: (L ++ CC)) in H2;[|auto].
      apply contractionK4 in H2;auto.
      SLSolve.
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
      rewrite H... perm.
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
      perm. 
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
   mt i = true -> u i = true -> seqN theory n ((B++[(i,F)])++[(loc,F)]) L X -> 
   seqN theory n (B++[(i,F)]) L X.
  Proof with sauto;solveLL.
  intro.
  induction n using strongind;intros... 
  * inversion H1...
    checkPermutationCases H4.
    checkPermutationCases H5.
    init2 i0 ((i,F)::x0).
    rewrite <- H6 in H2.
    rewrite <- H7 in H2.
    rewrite app_assoc_reverse in H2.
    SLSolve.  simpl;auto.
    rewrite H5...
    inversion H5...
    rewrite <- H7 in H6.
    rewrite <- H6 in H2.
    SLSolve.
    inversion H5...
   * inversion H2...
    checkPermutationCases H5.
    checkPermutationCases H6.
    init2 i0 ((i,F)::x0).
    rewrite <- H7 in H3.
    rewrite <- H8 in H3.
    rewrite app_assoc_reverse in H3.
    SLSolve.  simpl;auto.
    rewrite H6...
    inversion H6...
    rewrite <- H8 in H7.
    rewrite <- H7 in H3.
    SLSolve.
    inversion H6...
    - 
     repeat rewrite getUApp' in H5.
     repeat rewrite getUApp' in H6.
     repeat rewrite getLApp' in H7.
     simpl in H5.
     simpl in H6.
     simpl in H7.
     rewrite H1 in H5.
     rewrite H1 in H6.
     rewrite H1 in H7.
     rewrite locu in H5.
     rewrite locu in H6.
     rewrite locu in H7...
     eapply @tri_tensor with (M:=M) (N:=N) (B:=getU B ++ getL B0 ++ [(i, F)]) (D:=getU B ++ getL D ++ [(i, F)]);CleanContext.
      rewrite app_assoc.
      eapply H...
      eapply exchangeCCN. 
      2:{ exact H8. }
      rewrite cxtDestruct.
       CleanContext...
      rewrite <- H5... 
      rewrite app_assoc.
      eapply H...
      eapply exchangeCCN. 
      2:{ exact H9. }
      rewrite cxtDestruct.
      CleanContext.
      rewrite <- H6... 
    - eapply exchangeCCN with (CC:=(B ++ [(i0, F0)]) ++ [(i, F)])... 
      apply H...
      eapply exchangeCCN. 
      2:{ exact H4. }
      perm.
    - decide1 F0 L'. 
    - apply in_app_or in H7...
      { decide2u i0 F0. }
        inversion H3...
        decide2u i F0.
        apply in_or_app.
        right;firstorder. 
    - eapply Remove_Permutation_Ex2 with (M:=(loc, F)::([(i, F)]++B) ) in H7;auto...
      inversion H7... solveSubExp.
      inversion H13... 
      decide2l i0 F0 (l0++[(i,F)]).
      apply Remove_app_tail...
      apply H...
      eapply exchangeCCN. 
      2:{ exact H8. }
      rewrite <- H9. perm.
      - decide3 F0. 
    - existential t.
    - apply InvSubExpPhase in H5...
      checkPermutationCases H5.
      -- rewrite H5 in H6.
         assert(False).
         apply locAlone in H4.
         apply H4... left. 
         (* Add This Case *)
         autounfold in H6.
         apply Forall_app in H6...
         apply Forall_and_inv in H12...
         inversion H13...
         contradiction. 
      -- checkPermutationCases H5.
         rewrite H5 in H8.
         assert(False).
         apply locAlone in H4.
         apply H4... left. 
         (* Add This Case *)
         autounfold in H8.
         apply Forall_app in H8...
          apply Forall_and_inv in H13...
         inversion H14...
         contradiction.         
         checkPermutationCases H10.
         { (* m4 i = true *)
          assert( Permutation x ((i,F)::x4)). 
               { rewrite H10. perm. }
          (* colocar esse caso *) 
          eapply GenK4Rel with (C4:=(i,F)::x4) (CK:=x0) (CN:=x3)...    
          rewrite H3 in H6;auto.
          rewrite H5 in H9.
          SLSolve.
          rewrite <- H13.
          rewrite <- H12...
          rewrite H3 in H7... 
               eapply HeightGeqCEx.
               2:{ exact H11. }
               rewrite H3. simpl. perm.
               rewrite H3...   } 
        eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=x3)...
       rewrite H5 in H9;auto.
       SLSolve.
             rewrite <- H13...
             rewrite H12...
             rewrite H10...
   - apply InvSubExpPhase in H4...
      checkPermutationCases H4.
      -- assert(SetK4 i0 [(loc, F)]).
         rewrite H4 in H6.
         SLSolve.
         inversion H3...
         solveSubExp.
      -- checkPermutationCases H4.
         assert(SetK i0 [(loc, F)]).
         rewrite H4 in H8.
         SLSolve.
         
         assert(i0 <> loc).
         intro...
         solveSignature.
         apply locSetK2 in H3... 
         checkPermutationCases H10.
         { (* m4 i = true *)
          assert( Permutation x ((i,F)::x4)). 
               { rewrite H10. perm. }
          (* colocar esse caso *) 
          eapply @tri_bangD with (i:=i0)... 
          eapply GenK4Rel with (C4:=(i,F)::x4) (CK:=x0) (CN:=x3)...
          SLSolve.     
          rewrite H3 in H6;auto.
          rewrite H4 in H9.
          SLSolve.
          rewrite <- H13.
          rewrite <- H12...
          rewrite H3 in H7... 
               eapply HeightGeqCEx.
               2:{ exact H11. }
               rewrite H3. simpl. perm.
               rewrite H3...   }
          eapply @tri_bangD with (i:=i0)...      
        eapply GenK4Rel with (C4:=x) (CK:=x0) (CN:=x3)...
        intro... solveSignature. 
       rewrite H4 in H9;auto.
       SLSolve.
             rewrite <- H13...
             rewrite H12...
             rewrite H10...
             
   -- intro... solveSignature.                        
    Qed.
 
   Lemma ContractionL : forall n B C L X, 
   SetU C -> SetT C -> seqN theory n (B++C++Loc C) L X -> 
   seqN theory n (B++C) L X.
  Proof with sauto.
    intros.
    revert dependent B.
    revert dependent X.
    revert dependent L.
    revert dependent n.
    induction C;intros...
    simpl in H1. CleanContext.
    destruct a as [b F].
    
   eapply exchangeCCN with (CC:=(B ++ C) ++ [(b, F)])...
   perm.
   apply ContractionLoc...
   SLSolve.
   SLSolve.
   eapply exchangeCCN with (CC:=(B ++ [(loc, F)] ++ [(b, F)]) ++ C)...
   perm.
    apply IHC...
        SLSolve.
    SLSolve.
    eapply exchangeCCN.
    2:{ exact H1. }
    simpl. perm.
  Qed.
  
  Lemma ContractionL' : forall B C L X, 
   SetU C -> SetT C -> seq theory (B++C++Loc C) L X -> 
   seq theory (B++C) L X.
  Proof with sauto.
    intros.
    apply seqtoSeqN in H1.
    destruct H1.
    eapply seqNtoSeq with (n:=x).
    apply ContractionL...
  Qed.

  
  Lemma Loc_Unb : forall n B C L X, 
   SetU C -> SetT C -> seqN theory n (B++Loc C) L X -> 
   seqN theory n (B++C) L X.
  Proof with subst;auto.
    intros.
    apply  ContractionL...
    eapply exchangeCCN with (CC:=(B++Loc C) ++ C)...
    perm. 
    apply weakeningGenN_rev...
  Qed.  

Lemma Loc_Unb' : forall  B C L X, 
   SetU C -> SetT C -> seq theory (B++Loc C) L X -> 
   seq theory (B++C) L X.
  Proof with subst;auto.
    intros.
    apply  ContractionL'...
    eapply exchangeCC with (CC:=(B++Loc C) ++ C)...
    perm. 
    apply weakeningGen_rev...
  Qed.  
 
 Lemma Derivation1 D M F : 
 seq theory D M (>> F) -> seq theory D M (> [F]).
 Proof with sauto.
 intros.
 destruct(PositiveOrRelease F).
 store... intro.
 inversion H0;inversion H1...
 decide1 F. intro. 
 inversion H0;inversion H1...
 inversion H;inversion H0...
Qed. 
  
  Lemma InvBangTN i j B P : u i = true -> mt i = true ->
          seqN theory  j B [] (>> i ! P) -> seqN theory (j-1) B [] (> [P]).
  Proof with sauto.
  intros Hu Hm Hj.
  inversion Hj...
  inversion H0.
  eapply InvSubExpPhaseU in H4;auto. 
  destruct H4 as [C4 H4].
  destruct H4 as [CK H4].
  destruct H4 as [CN H4]...
  rewrite H.
  rewrite app_assoc. 
  apply weakeningGenN_rev;auto.
  rewrite setUtoGetU in H9;auto.
  rewrite setUtoGetU in H9;auto.
  apply ContractionL...
  eapply (SetTKClosure Hm)...
  rewrite SetTPlusT in H9.
  eapply exchangeCCN with (CC:=(C4 ++ Loc CK) ++ CK)...
  perm.
  apply weakeningGenN_rev;auto.
  eapply @HeightGeq with (n:=n - length (C4 ++ CK) - 1)...
  lia.
   eapply (SetTK4Closure Hm)... 
 Qed. 
 
  Lemma InvBangT i j B P : u i = true -> mt i = true ->
          seqN theory j B [] (>> i ! P) -> seq theory B [] (> [P]).
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
          tensor x N B D.
          apply IHn with (F:=F)...
          rewrite <- H3;auto.
          tensor M x B D.
          apply IHn with (F:=F)...
          rewrite <- H3;auto.
        - oplus1.
          apply IHn with (F:=F)...
        - oplus2.
          apply IHn with (F:=F)...
        - release.
          apply IHn with (F:=F)...
        - solveLL.
          apply IHn with (F:=F)...
        - solveLL.
          apply IHn with (F:=F)...
        - solveLL.
          apply IHn with (F:=F)...
          apply IHn with (F:=F)...
        - solveLL.
          apply IHn with (F:=F)...
        - solveLL.
          apply IHn with (F:=F)...
          rewrite perm_swap;auto.
        - inversion H4...
          decide3 F. 
          decide1 F0 l2. 
          apply IHn with (F:=F)...
        - decide2u i F0. 
          apply IHn with (F:=F)...
        - decide2l i F0 B'. 
          apply IHn with (F:=F)...
        - decide3 F0. 
          apply IHn with (F:=F)...
        - existential t.
          apply IHn with (F:=F)...
        - solveLL. 
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
 
  End MoreWeakening.
End FLLBasicTheory.
