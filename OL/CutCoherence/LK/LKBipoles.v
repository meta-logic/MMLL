Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.Bipoles.

Set Implicit Arguments.


(** ** Rules of the encoded proof system *)
Section LKInferenceRules.

Context {SI : Signature}.
Context {SY : OLSyntax}.

  Inductive ContantEnc := TOPZERO | ZEROTOP .
  
  Definition CteRulesDefs (t:ContantEnc) (s:Side):=
    match t,s with
    | TOPZERO, Left => Top
    | ZEROTOP, Left => Zero
    | TOPZERO, Right => Zero
    | ZEROTOP, Right => Top
    end.
 
  Inductive RulesEnc := PLUSWILK | WILKPLUS  | TENSORPAR .
  
  Definition RulesDefs (t:RulesEnc) (s:Side) (A B : uexp)  :=
       match t,s with
      | PLUSWILK, Left => AOr (d|A|) (d|B|)
      | PLUSWILK, Right => AAnd (u|A|) ( u|B|)
      | WILKPLUS, Left => AAnd (d|A|) (d|B|)
      | WILKPLUS, Right => AOr (u|A|) ( u|B|)
      | TENSORPAR, Left => MAnd (u|A|) (d|B|)
      | TENSORPAR, Right => MOr (d|A|) (u|B|) 
      end.  

  Inductive QEnc := ALLSOME | SOMEALL .
  
  Definition QDefs (t:QEnc) (s:Side) (FX : uexp -> uexp):=
    match t,s with 
    | ALLSOME, Left =>  Some (fun x => d| (FX x)|) 
    | ALLSOME, Right => All (fun x => u| (FX x)|)
    | SOMEALL, Left =>  All (fun x => d| (FX x)|)
    | SOMEALL, Right => Some (fun x => u| (FX x)|)
    end .
 
  Class OORules :=
    {
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc;
      rulesQ :   quantifiers -> QEnc
    }.
  
End LKInferenceRules.
 
Section CutCohBipoles.
  Context {SI : Signature}.
 
Inductive Constants := TT | FF.
Inductive Connectives := AND | OR | IMP.
Inductive UConnectives := . 
Inductive Quantifiers := ALL | SOME.

Global Instance SimpleOLSig : OLSyntax:=
  {|
    OLType := nat;
    constants := Constants;
    uconnectives := UConnectives;
    connectives := Connectives ;
    quantifiers := Quantifiers
  |}.
 
 Instance TT_BODY : CteBody := {
    cte := TT;
    rc_rightBody := CteRulesDefs ZEROTOP Right;
    rc_leftBody := CteRulesDefs ZEROTOP Left
  }.
  
 Instance FF_BODY : CteBody := {
    cte := FF;
    rc_rightBody := CteRulesDefs TOPZERO Right;
    rc_leftBody := CteRulesDefs TOPZERO Left
  }.
  
 Instance AND_BODY : BinBody := {
    con := AND;
    rb_rightBody := RulesDefs PLUSWILK Right;
    rb_leftBody := RulesDefs PLUSWILK Left
  }.
  
 Instance OR_BODY : BinBody := {
    con := OR;
    rb_rightBody := RulesDefs WILKPLUS Right;
    rb_leftBody := RulesDefs WILKPLUS Left
  }.
 
 Instance IMP_BODY : BinBody := {
    con := IMP;
    rb_rightBody := RulesDefs TENSORPAR Right;
    rb_leftBody := RulesDefs TENSORPAR Left
  }.

 Instance ALL_BODY : QuBody := {
    qt := ALL;
    rq_rightBody := QDefs ALLSOME Right;
    rq_leftBody := QDefs ALLSOME Left
  }.
  
 Instance SOME_BODY : QuBody := {
    qt := SOME;
    rq_rightBody := QDefs SOMEALL Right;
    rq_leftBody := QDefs SOMEALL Left
  }.
  
  Section CutCoherence.
  
Instance TT_CUTCOHERENT : CteCutCoherent TT_BODY .
Proof.
   constructor.
   simpl. solveLL.
 Defined.  
 
  
Instance FF_CUTCOHERENT : CteCutCoherent FF_BODY .
Proof. 
   constructor.
   simpl. solveLL. 
 Defined.
  
  
Instance AND_CUTCOHERENT : BinCutCoherent (RCUT:=CUTLN) AND_BODY .
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl. 
  LLStore.
  LLWith.
  all: LLStore.
  -  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H.
      LLTensor [d^| F |] [AOr (u^| F |) (u^| G |)]. 
             LLRelease. solveLL.
             LLRelease. solveLL.
             LFocus(AOr (u^| F |) (u^| G |)) [u| F |].
   -  TFocus(CUTL G ).
      apply ltn with (m:=m)...
      inversion H.
      LLTensor [d^| G |] [AOr (u^| F |) (u^| G |)]. 
             LLRelease. solveLL.
             LLRelease. solveLL.
             LFocus(AOr (u^| F |) (u^| G |)) [u| G |]. 
 Defined.  
 
 
Instance OR_CUTCOHERENT : BinCutCoherent (RCUT:=CUTLN) OR_BODY .
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl. 
  LLWith.
  all: do 2 LLStore.
  -  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H.
      LLTensor  [AOr (d^| F |) (d^| G |)] [u^| F |]. 
             LLRelease. LLStore.
             LFocus(AOr (d^| F |) (d^| G |)) [d| F |].
             LLRelease. solveLL.
   -  TFocus(CUTL G ).
      apply ltn with (m:=m)...
      inversion H.
      LLTensor  [AOr (d^| F |) (d^| G |)] [u^| G |]. 
             LLRelease. LLStore.
             LFocus(AOr (d^| F |) (d^| G |)) [d| G |]. 
             LLRelease. solveLL.
    Defined.       

Instance IMP_CUTCOHERENT : BinCutCoherent (RCUT:=CUTLN) IMP_BODY .
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl.
  LLStore. 
  LLPar.
  do 2 LLStore.
  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H.
  LLTensor  [d^| G |; MAnd (d^| F |) (u^| G |)] [u^| F |]. 
             LLRelease. LLStore.
  TFocus(CUTL G ).
       eapply ltn with (m:=m)... 
       inversion H.
  LLTensor  [d^| G |] [d| F |; MAnd (d^| F |) (u^| G |)].  
             LLRelease. solveLL. 
   LLRelease. LLStore. 
    LFocus(MAnd (d^| F |) (u^| G |)) [u|G |; d| F |].
    LLTensor [d|F |] [u|G |].
             LLRelease. solveLL. 
 Defined.          
  
(** We cannot prove that the size of (FX t) is independent of t
  (assuming that FX is uniform and t is proper). This is indeed the
  case since uniform functions cannot do patter matching to return
  structurally different formulas. Hence, the following axiom is
  admitted in order to prove that the definitions of the connectives
  are cut-coherent  *)
  Axiom OLSize: forall FX t t' n, uniform FX -> proper t -> proper t' -> lengthUexp (FX t) n -> lengthUexp (FX t') n .
  
Instance ALL_CUTCOHERENT : QuCutCoherent (RCUT:=CUTLN) ALL_BODY .
Proof with sauto. 
  constructor.
  intros *. intros uFX uFX' eqF lenF isF.
  simpl.
  LLStore. 
  LLForall.  
  solveUniform. 
  specialize (isF _ H).
  LLStore.
  TFocus(CUTL (FX' x) ).
       eapply ltn with (m:=n)...
  rewrite <- eqF...
  rewrite <- eqF...
  refine (OLSize _ _ _ lenF)...
  solveUniform.
  inversion H0.
  LLTensor [d^| FX' x |] [∃{ fun x0 : expr Syntax.con => u^| FX x0 |}].
  solveLL.
  LLRelease. LLStore.
  rewrite perm_takeit_8.
  LFocus.
  LLExists x.
  rewrite eqF...
Defined.  
           
Instance SOME_CUTCOHERENT : QuCutCoherent (RCUT:=CUTLN) SOME_BODY .
Proof with sauto. 
  constructor.
  intros *. intros uFX uFX' eqF lenF isF.
  simpl.
  LLForall.  
  solveUniform.
  do 2 LLStore. 
  specialize (isF _ H).
  TFocus(CUTL (FX x) ).
       eapply ltn with (m:=n)...
  rewrite eqF...
  rewrite <- eqF...
  refine (OLSize _ _ _ lenF)...
  solveUniform.
  inversion H0.
  LLTensor [∃{ fun x0 : expr Syntax.con => d^| FX' x0 |}] [u^| FX x |] .
  2: solveLL.
  LLRelease. LLStore.
  rewrite perm_takeit_8.
  LFocus.
  LLExists x.
  rewrite eqF...
Defined.  

End CutCoherence.

  Inductive buildTheoryCons : oo ->  Prop := 
  | cteTTR : isOLFormula (t_cons TT_BODY.(cte)) -> 
        buildTheoryCons (CteBipole TT_BODY Right)
  | cteTTL : isOLFormula (t_cons TT_BODY.(cte)) -> 
        buildTheoryCons (CteBipole TT_BODY Left)
  | cteFFR : isOLFormula (t_cons FF_BODY.(cte)) -> 
        buildTheoryCons (CteBipole FF_BODY Right)
  | cteFFL : isOLFormula (t_cons FF_BODY.(cte)) -> 
        buildTheoryCons (CteBipole FF_BODY Left).
 
Inductive buildTheory : oo ->  Prop :=  
  | bconANDR : forall F G, 
          isOLFormula ( t_bin AND_BODY.(con) F G) ->
          buildTheory  (BinBipole AND_BODY Right F G) 
  | bconANDL : forall F G, 
          isOLFormula ( t_bin AND_BODY.(con) F G) ->
          buildTheory  (BinBipole AND_BODY Left F G)          
  | bconORR : forall F G, 
          isOLFormula ( t_bin OR_BODY.(con) F G) ->
          buildTheory  (BinBipole OR_BODY Right F G) 
  | bconORL : forall F G, 
          isOLFormula ( t_bin OR_BODY.(con) F G) ->
          buildTheory  (BinBipole OR_BODY Left F G)           
  | bconIMPR : forall F G, 
          isOLFormula ( t_bin IMP_BODY.(con) F G) ->
          buildTheory  (BinBipole IMP_BODY Right F G) 
  | bconIMPL : forall F G, 
          isOLFormula ( t_bin IMP_BODY.(con) F G) ->
          buildTheory  (BinBipole IMP_BODY Left F G) .          
  
  Inductive buildTheoryBind : oo ->  Prop := 
  | bqALLR : forall FX, uniform FX -> 
              isOLFormula (t_quant ALL_BODY.(qt) FX) -> 
              buildTheoryBind  (QuBipole ALL_BODY Right FX)
  | bqALLL : forall FX, uniform FX -> 
              isOLFormula (t_quant ALL_BODY.(qt) FX) -> 
              buildTheoryBind  (QuBipole ALL_BODY Left FX)
  | bqSOMER : forall FX, uniform FX -> 
              isOLFormula (t_quant SOME_BODY.(qt) FX) -> 
              buildTheoryBind  (QuBipole SOME_BODY Right FX)
  | bqSOMEL : forall FX, uniform FX -> 
              isOLFormula (t_quant SOME_BODY.(qt) FX) -> 
              buildTheoryBind  (QuBipole SOME_BODY Left FX).
  
 (** A theory containing only the logical rules and init *)
  Inductive LKTheory {i:subexp} : oo -> Prop :=
  | ooth_consC : forall OO, buildTheoryCons OO ->  LKTheory OO
  | ooth_rulesC : forall OO, buildTheory OO ->  LKTheory OO
  | ooth_initC : forall OO, isOLFormula OO -> LKTheory (RINIT OO)
  | ooth_binderC : forall OO, buildTheoryBind OO -> LKTheory OO
  | ooth_posC : forall OO, mt i = true -> isOLFormula OO -> LKTheory (POS OO i) 
  | ooth_negC : forall OO, mt i = true -> isOLFormula OO -> LKTheory (NEG OO i) 
.          

 (** A theory containing the logical rules, init and cut *)
  Inductive LKTheoryCut (n:nat) {i:subexp} : oo -> Prop :=
  | oothc_consC : forall OO, buildTheoryCons OO ->  LKTheoryCut n OO
  | oothc_rulesC : forall OO, buildTheory OO ->  LKTheoryCut n OO
  | oothc_initC : forall OO, isOLFormula OO -> LKTheoryCut n (RINIT OO)
  | oothc_binderC : forall OO, buildTheoryBind OO -> LKTheoryCut n OO
  | oothc_posC : forall OO , mt i = true -> isOLFormula OO -> LKTheoryCut n (POS OO i) 
  | oothc_negC : forall OO , mt i = true -> isOLFormula OO -> LKTheoryCut n (NEG OO i) 
  | oothc_cutln : forall OO, CUTLN n (CUTL OO) -> LKTheoryCut n (CUTL OO).
  
 Lemma CuteRuleNBound {SIU: UnbSignature}: forall h n B L X ,  seqN (CUTLN n) h B L X ->
                                             forall m, n<=m -> seq (CUTLN m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (CUTLN n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (CUTLN m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n) ;solveF
                   );clear Hs
             end;try solveLL;auto.
    -         
    rewrite H3. 
    LLTensor M N B0 D.
    - 
    LFocus F ;eauto.
    -
    UFocus i F;eauto ...
    -
    BFocus i F;eauto ...
    -
    TFocus F;eauto ...
    inversion H3...
    apply @ltn with (m:= m0)...
    -
    LLExists t.
    -
    apply H4 in properX...
    eapply H  with (m:= h) (n:= n) ;solveF.
    - 
   apply InvSubExpPhaseU in H4...
   2:{ apply allU. }
   createWorld.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia.              
    - 
   apply InvSubExpPhaseU in H3...
   2:{ apply allU. }
   createWorld i.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    solveSignature1.
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia. solveSignature1.
  Qed.
  
  
  Lemma CuteRuleN : forall n F, CUTLN n F ->
                                             forall m, n<=m -> CUTLN m F.
  Proof with sauto.
    intros.
    inversion H...
    econstructor;eauto.
    (transitivity n);auto.
  Qed.

  Lemma CuteRuleNBound' {USI: UnbSignature}: forall n B L X ,
      seq (CUTLN n)  B L X ->
      forall m, n<=m -> seq (CUTLN m) B L X .
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  
 (** There are no (object logic) formulas of size 0 *)
  Lemma CuteRuleN0 : forall F, ~ (CUTLN 0 F).
  Proof with solveF.
    intros F Hn.
    inversion Hn...
    generalize (LengthFormula H H0); intro.
    lia.
  Qed.
  
 Definition LK i := LKTheory (i:=i).
 Definition LKC i n := LKTheoryCut (i:=i) n.
 
 Local Hint Constructors  LKTheoryCut LKTheory  : core.
 Local Hint Unfold RINIT CUTL CUTC  : core.
 Local Hint Unfold LK LKC : core.

Lemma CutRuleNBound {SIU: UnbSignature}: forall h i n B L X ,  seqN (LKC i n) h B L X ->
                         forall m, n<=m -> seq (LKC i m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i0 C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (LKC i n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (LKC i m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (B:= B1);solveF 
                   );clear Hs
             end;solveLL;auto.
    -         
    rewrite H3. LLTensor M N B0 D.
    -
    LFocus F ;eauto.
    -
    UFocus i0 F;eauto ...
    -
    BFocus i0 F;eauto ...
    -
    TFocus F;eauto ...
    unfold LKC in H3.
    unfold LKC.
    inversion H3...
    eapply oothc_cutln.
     eapply CuteRuleN;eauto.
    -
    LLExists t.
    -
    apply H4 in properX.
     eapply H  with (m:= h) (n:= n)  ;solveF.
    - 
       apply InvSubExpPhaseU in H4...
   2:{ apply allU. }
   createWorld.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia.              
    - 
   apply InvSubExpPhaseU in H3...
   2:{ apply allU. }
   createWorld i0.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    solveSignature1.
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia. solveSignature1.
   Qed. 

 
  Lemma CutRuleNBound' {SIU: UnbSignature}:  forall i n B L X ,  
  seq (LKC i n)  B L X ->
                         forall m, n<=m -> seq (LKC i m) B L X .
  Proof with solveF.
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CutRuleNBound;eauto.
    
  Qed.
  
  (** Some easy equivalences on the  above theories *)
 Lemma OOTheryCut0 : forall i F, 
 LK i F <-> (LKC i 0) F.
 Proof. 
    intros.
    autounfold.
    split;intro H ;inversion H;subst;auto.
    *
    inversion H0;subst.
    assert (m =  0%nat) by lia;subst.
    generalize (LengthFormula H3 H4);intro.
    lia.
  Qed.
   
  Lemma TheoryEmb1 : forall n i F  ,  
  LK i F -> (LKC i n) F.
 Proof.
    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.
  
  Lemma TheoryEmb2 : forall n i F  , ((CUTLN n) F) -> (LKC i n) F.
Proof.
    intros.
    inversion H;subst.
    apply oothc_cutln;auto.
  Qed.
  
 End CutCohBipoles.

Global Hint Constructors  LKTheoryCut LKTheory  : core.
Global Hint Unfold RINIT CUTL CUTC  : core.
Global Hint Unfold LK LKC : core.