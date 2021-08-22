(** * OL-Cut Elimination  *)

(** The procedure formalized here is tailored to the case of
object-logics (OL) where formulas on both the left and the right side
of the sequent can be weakened and contacted. Then, we assume that all
of them are stored into the classical context of LL. *)

Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.OLTactics.
Require Export MMLL.OL.CutCoherence.OLPosNeg.
Import MMLL.Misc.Permutations.
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.


(** ** Rules of the encoded proof system *)
Section OLInferenceRules.

Context {SI : Signature}.
Context {USI : UnbSignature}.
Context {SY : OLSyntax}.


  Inductive Side := Left | Right .

 (** INIT and CUT rules *)
  Definition RINIT (F:uexp) : oo := (perp (up  F) )  ** (perp (down F) ) .

  (** Constants in this kind of systems can be obly TOP/ZERO or
  ZERO/TOP (in order to be cut-coherent) *)

  Inductive ContantEnc := TOPZERO | ZEROTOP .
  
  Definition CteRulesDefs (t:ContantEnc) (s:Side):=
    match t,s with
    | TOPZERO, Left => top
    | ZEROTOP, Left => zero
    | TOPZERO, Right => zero
    | ZEROTOP, Right => top
    end.
  
  (** Both left and right atoms must be marked with the exponential ?
  in order to store all the atoms into the classical context. The
  following pairs of formulas are all cut-coherent:
                        
   - [PARTENSOR]: On the left rule, it takes the atom [A * B] and
   produces one premise containing both [A] and [B] (stored in the
   classical context). In the right rule, it generates two
   premises. This is the typical encoding for conjuction-like
   connectives.
   
   - [TENSORPAR]: On the left rule, it generates two premises and, on
   the right side, it generates only one premise. This is the typical
   encoding for disjunction-like connectives.

   - [TENSORPAREXCH]: Similar to the previous one but [A] goes to the
   right premise and [B] to the left premise. This is the typical
   encoding for a implication-like connective.

   *)

  Inductive RulesEnc := PARTENSOR | TENSORPAR | TENSORPAREXCH .
  
  Definition RulesDefsC (t:RulesEnc) (s:Side) (A B : uexp)  :=
       match t,s with
      | PARTENSOR, Left => (d|A|) op (d|B|)
      | PARTENSOR, Right => (u|A|) & ( u|B|)
      | TENSORPAR, Left => (d|A|) & (d|B|)
      | TENSORPAR, Right => (u|A|) op ( u|B|)
      | TENSORPAREXCH, Left => (u|A|) ** (d|B|)
      | TENSORPAREXCH, Right => (d|A|) $ (u|B|) 
      end.
  
  Definition RulesDefsI (t:RulesEnc) (s:Side) (A B : uexp) {i: subexp}  :=
       match t,s with
      | PARTENSOR, Left => (d|A|) op (d|B|)
      | PARTENSOR, Right => (u|A|) & ( u|B|)
      | TENSORPAR, Left => (d|A|) & (d|B|)
      | TENSORPAR, Right => (u|A|) op ( u|B|)
      | TENSORPAREXCH, Left => (u|A|) ** (d|B|)
      | TENSORPAREXCH, Right => i ! ((d|A|) $ (u|B|))
    end.
  
  
  Inductive MEnc := QUESTBANG .      
  Definition MDRulesDefs (t:MEnc) (s:Side) (A : uexp) (i: subexp)  :=
       match t,s with
      | QUESTBANG , Left => i ? (d|A|)
      | QUESTBANG , Right => i ! (u|A|)
     end.
      
 
  (** We assume the usual encoding for the quantifiers *)
  Inductive QEnc := ALLSOME | SOMEALL .
  
  Definition QDefs (t:QEnc) (s:Side) (FX : uexp -> uexp):=
    match t,s with 
    | ALLSOME, Left =>  E{ fun x => d| (FX x)|} 
    | ALLSOME, Right => F{ fun x => u| (FX x)|}
    | SOMEALL, Left =>  F{ fun x => d| (FX x)|}
    | SOMEALL, Right => E{ fun x => u| (FX x)|}
    end .
  
 
  Class OORules :=
    {
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc;
      rulesU : uconnectives -> MEnc;
      rulesQ :   quantifiers -> QEnc
    }.
    
  
End OLInferenceRules.

(** ** Cut-Coherence

This section shows that right and left rules are cut-coherent by applying the
rule [RCUTcN] on subformulas 
*)
(** Building the inference rules (bipoles) *)
Section Bipoles.
  Context `{OLR: OORules}.
    Context `{SI: Signature}.
Context {USI : UnbSignature}.
  
  (** building rules for constants *)
  Definition makeRuleConstant (lab : constants) (s:Side) :=
    match s with
    | Right => ( u^|t_cons lab| ) ** (CteRulesDefs (rulesCte lab) s)
    | Left => ( d^|t_cons lab| ) ** (CteRulesDefs (rulesCte lab) s)
    end.

  (** building rules for connectives *)
  Definition makeRuleBinC (lab : connectives) (s:Side):=
    fun (A B :uexp) =>
      match s with
      | Right => (u^| t_bin lab A B|) ** (RulesDefsC  (rulesBin lab) s A B)
      | Left => (d^| t_bin lab A B|) ** (RulesDefsC (rulesBin lab) s A B)
      end.
  
  Definition makeRuleBinI (lab : connectives) (s:Side) {i: subexp} :=
    fun (A B :uexp) =>
      match s with
      | Right => (u^| t_bin lab A B|) ** (RulesDefsI (i:=i) (rulesBin lab) s A B)
      | Left => (d^| t_bin lab A B|) ** (RulesDefsI (i:=i) (rulesBin lab) s A B)
      end.
  
   (** building rules for quantifiers *)
  Definition makeRuleQ (lab : quantifiers) (s:Side):=
    fun (FX :uexp -> uexp) =>
      match s with
      | Right => (u^| t_quant lab FX|) ** (QDefs (rulesQ lab) s FX)
      | Left => (d^| t_quant lab FX|) **  (QDefs (rulesQ lab) s FX)
      end.

  Definition makeRuleM (lab : uconnectives) (s:Side):=
    fun (A: uexp) (i:subexp) =>
      match s with
      | Right => (u^| t_ucon lab A|) ** (MDRulesDefs (rulesU lab) s A i)
      | Left => (d^| t_ucon lab A|) **  (MDRulesDefs (rulesU lab) s A i)
      end.

  Hint Unfold makeRuleConstant makeRuleBinC makeRuleBinI makeRuleM makeRuleQ  : core.

 (*  Theorem RulesLKIsFormula : forall T S A B,
      isFormula ((LKRulesDefs T S A B) ).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.
  
Theorem LKIsFormula : forall T S A B,
      isFormula ((makeRuleBinLK T S A B) ).
    intros.
    destruct S;simpl;auto using RulesLKIsFormula.
  Qed.

 Theorem RulesLJIsFormula : forall T S A B i,
      isFormula ((LJRulesDefs T S A B i) ).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.
  
 Theorem LJIsFormula : forall T S A B i,
      isFormula ((makeRuleBinLJ (i:=i) T S A B) ).
    intros.
    destruct S;simpl;auto using RulesLJIsFormula.
  Qed.
 *)
  Theorem MRulesIsFormula : forall T S A i,
    isFormula ((MDRulesDefs T S A i) ).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.
  
  Theorem MRIsFormula : forall T S A i,
    isFormula ((makeRuleM T S A i) ).
    intros.
    destruct S;simpl;auto using MRulesIsFormula.
  Qed.
  
  
 (*  Theorem RulesLKPerpIsFormula : forall T S A B,
      isFormula ((LKRulesDefs T S A B) ^).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.

  Theorem RulesLJPerpIsFormula : forall T S A B i,
      isFormula ((LJRulesDefs T S A B i) ^).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.
 *)
 Theorem RulesMDPerpIsFormula : forall T S A i,
      isFormula ((MDRulesDefs T S A i) ^).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.

Theorem QPerpIsFormula: forall T S FX,
      uniform FX -> 
      isFormula ((QDefs T S FX) ^).
    intros.
    destruct T;destruct S;simpl;auto;
      repeat constructor;auto.
  Qed.


  Theorem QIsFormula: forall T S FX,
      uniform FX -> 
      isFormula ((QDefs T S FX) ).
    intros.
    destruct T;destruct S;simpl;auto;
      repeat constructor;auto.
  Qed.

  Theorem CtesIsFormula : forall C S,
      isFormula (makeRuleConstant C S).
    intros.
    destruct S;simpl;auto.
    destruct (rulesCte C);simpl;auto.
    destruct (rulesCte C);simpl;auto.
  Qed.

  
  Theorem RulesQIsFormula : forall T S FX,
      uniform FX ->
      isFormula ((makeRuleQ T S FX) ).
    intros.
    destruct S;simpl; destruct (rulesQ T);
      repeat constructor;auto.
  Qed.
  
  
  (** This is the FLL logical theory including the right and left
    rules for the connectives and constants *)
  Inductive buildTheoryCons : oo ->  Prop := 
  | bcteR : forall C, isOLFormula (t_cons C) -> buildTheoryCons (makeRuleConstant C Right)
  | bcteL : forall C, isOLFormula (t_cons C) -> buildTheoryCons (makeRuleConstant C Left).
  
  Inductive buildTheoryBind : oo ->  Prop := 
  | bqR : forall C FX, uniform FX -> isOLFormula (t_quant C FX) -> buildTheoryBind  (makeRuleQ C Right FX)
  | bqL : forall C FX, uniform FX -> isOLFormula (t_quant C FX) -> buildTheoryBind  (makeRuleQ C Left FX).
  
  Inductive buildTheoryI {i: subexp} : oo ->  Prop :=  
  | bconnRI : forall C F G, isOLFormula ( t_bin C F G) -> buildTheoryI  (makeRuleBinI (i:=i) C Right F G)  
  | bconnLI : forall C F G, isOLFormula ( t_bin C F G) -> buildTheoryI  (makeRuleBinI (i:=i) C Left F G).
  
  Inductive buildTheoryC : oo ->  Prop :=  
  | bconnRC : forall C F G, isOLFormula ( t_bin C F G) -> buildTheoryC  (makeRuleBinC C Right F G)  
  | bconnLC : forall C F G, isOLFormula ( t_bin C F G) -> buildTheoryC  (makeRuleBinC C Left F G).
  
   Inductive buildTheoryModal {i: subexp} : oo ->  Prop := 
  | bmR : forall i C A, isOLFormula (t_ucon C A) -> buildTheoryModal  (makeRuleM C Right A i)
  | bmL : forall i C A, isOLFormula (t_ucon C A) -> buildTheoryModal  (makeRuleM C Left A i).
  
  (** A theory containing only the logical rules and init *)
  Inductive OLTheoryC : oo -> Prop :=
  | ooth_consC : forall OO, buildTheoryCons OO ->  OLTheoryC OO
  | ooth_rulesC : forall OO, buildTheoryC OO ->  OLTheoryC OO
  | ooth_initC : forall OO, isOLFormula OO -> OLTheoryC (RINIT OO)
  | ooth_binderC : forall OO, buildTheoryBind OO -> OLTheoryC OO
  | ooth_posC : forall OO , isOLFormula OO -> OLTheoryC (POS OO loc) 
  | ooth_negC : forall OO , isOLFormula OO -> OLTheoryC (NEG OO loc) 
.

  Inductive OLTheoryI  {i a: subexp} : oo -> Prop :=
  | ooth_consI : forall OO, buildTheoryCons OO ->  OLTheoryI OO  
  | ooth_rulesI : forall OO, buildTheoryI (i:=i) OO ->  OLTheoryI OO
  | ooth_initI : forall OO, isOLFormula OO -> OLTheoryI (RINIT OO)
  | ooth_binderI : forall OO, buildTheoryBind OO -> OLTheoryI OO
  | ooth_posI : forall OO , m4 a = true -> mt a = true -> isOLFormula OO -> OLTheoryI (POS OO a) 
  | ooth_negI : forall OO , isOLFormula OO -> OLTheoryI (NEG OO loc) 
.

  Inductive OLTheoryM  {i a b: subexp} : oo -> Prop :=
  | ooth_consM : forall OO, buildTheoryCons OO ->  OLTheoryM OO  
  | ooth_rulesM : forall OO, buildTheoryC OO ->  OLTheoryM OO
  | ooth_initM : forall OO, isOLFormula OO -> OLTheoryM (RINIT OO)
  | ooth_posM : forall OO , isOLFormula OO -> OLTheoryM (POS OO loc) 
  | ooth_negM : forall OO , isOLFormula OO -> OLTheoryM (NEG OO loc) 
.

 Local Hint Constructors  OLTheoryI OLTheoryC OLTheoryM  : core.
 Local Hint Unfold RINIT : core.
  Lemma Init_inversion1 : forall h F D th,
      seqN th h [] D (>> RINIT F) -> Permutation D ([u| F |] ++ [d| F |]) .
  Proof with sauto.
    intros.
    FLLInversionAll...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct B) in H1.
    rewrite H3 in H1.
    rewrite H in H1.
    simpl in H1...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct D0) in H11.
    rewrite H4 in H11.
    rewrite H0 in H11.
    simpl in H11...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct D0) in H13.
    rewrite H4 in H13.
    rewrite H0 in H13.
    simpl in H13...
  Qed.  
    
   
 (*  Theorem TENSORPARInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
    LLExact H0.
  Qed.

  Theorem TENSORPARInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Right A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem TENSORPAREXCHInv : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (u| A |:: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
    LLExact H0.
  Qed.

  Theorem TENSORPAREXCHInv' : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Right A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem PARTensorInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem PARTensorInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Right A B ) .
    intros;simpl;solveLL;
      rewrite Permutation_app_comm;simpl;auto.
  Qed.
*)

Lemma emptyContext C : getU C = [] -> getL C =[] -> C = [].
Proof.
 intros.
 apply Permutation_nil.
 rewrite (cxtDestruct C).
 rewrite H; rewrite H0;auto. 
 Qed.
 
 
    Lemma FocusingInitRuleU : forall h F D B th,
      seqN th h B D (>> RINIT F) -> 
      Permutation D ([u| F |] ++ [d| F |]) \/ 
      (D = [u| F |] /\ In (d| F |) (second (getU B))) \/ 
      (D = [d| F |] /\ In (u| F |) (second (getU B))) \/
      (In (d| F |) (second (getU B)) /\ In (u| F |) (second (getU B))).
  Proof with sauto.
    intros.
    inversion H...
    - inversion H9; 
      inversion H10...
      + CleanContext.
        right.
        left.
        split;auto.
         eapply @InSecondInv with (i:=i)...
     
        rewrite H4.
        rewrite <- H17...
        CleanContext.
        rewrite (allU i)...
      + inversion H12.
      +  CleanContext.
        right.
        right.
        left.
        split;auto.
         eapply @InSecondInv with (i:=i)...
        rewrite H3.
        rewrite <- H12...
        CleanContext.
        rewrite (allU i)...
       + CleanContext. 
         do 3 right.
         split...
          eapply @InSecondInv with (i:=i0)...
     
         rewrite H4.
         rewrite <- H19...
         CleanContext.
         rewrite (allU i0)...
     
          eapply @InSecondInv with (i:=i)...
     
         rewrite H3.
         rewrite <- H12...
         CleanContext.
         rewrite (allU i)...
     
        + inversion H14.
        + inversion H1.
        + inversion H1.
        + inversion H13.
    - inversion H1. 
  Qed.  
 
  Theorem FocusingRightCRuleU : forall n D B C F G th,
      (seqN th n B D (>> makeRuleBinC C Right F G)) ->
 (exists m N, n = S m /\ Permutation D ((u|t_bin C F G|)::N) /\
                seqN th m B N  (>> RulesDefsC (rulesBin C) Right F G)) \/
   (exists m, n = S m /\ In (u| t_bin C F G |) (second B) /\
                seqN th m B D  (>> RulesDefsC (rulesBin C) Right F G)).
  Proof with sauto.
  intros.
  inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
     
    - CleanContext.
      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      right.
      exists n0.
      split;auto.
      split;auto.
      
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      rewrite H2...
      LLExact H10.
      inversion H6.
    - inversion H1.
  Qed.      

 
  Theorem FocusingRightIRuleU : forall n a D B C F G th,
      (seqN th n B D (>> makeRuleBinI (i:=a) C Right F G)) ->
 (exists m N, n = S m /\ Permutation D ((u|t_bin C F G|)::N) /\
                seqN th m B N  (>> RulesDefsI (i:=a) (rulesBin C) Right F G)) \/
   (exists m, n = S m /\ In (u| t_bin C F G |) (second B) /\
                seqN th m B D  (>> RulesDefsI (i:=a)  (rulesBin C) Right F G)).
  Proof with sauto.
  intros.
  inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
     
    - CleanContext.
      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      right.
      exists n0.
      split;auto.
      split;auto.
      
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      rewrite H2...
      LLExact H10.
      inversion H6.
    - inversion H1.
  Qed.  
  
 Theorem FocusingLeftCRuleU : forall n D B C F G th,
      (seqN th n B D (>> makeRuleBinC C Left F G )) ->
 (exists m N, n = S m /\ Permutation D ((d|t_bin C F G|)::N) /\
                seqN th m B N  (>> RulesDefsC (rulesBin C) Left F G)) \/
   (exists m, n = S m /\ In (d| t_bin C F G |) (second B) /\
                seqN th m B D  (>> RulesDefsC  (rulesBin C) Left F G)).
  Proof with sauto.
  intros.
  inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
       apply simplUnb in H5...
      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      
      rewrite H5...
      rewrite <- H13...
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
  Qed.
  
        
 Theorem FocusingLeftIRuleU : forall n a D B C F G th,
      (seqN th n B D (>> makeRuleBinI  (i:=a) C Left F G )) ->
 (exists m N, n = S m /\ Permutation D ((d|t_bin C F G|)::N) /\
                seqN th m B N  (>> RulesDefsI  (i:=a) (rulesBin C) Left F G)) \/
   (exists m, n = S m /\ In (d| t_bin C F G |) (second B) /\
                seqN th m B D  (>> RulesDefsI  (i:=a) (rulesBin C) Left F G)).
  Proof with sauto.
  intros.
  inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
       apply simplUnb in H5...
      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      
      rewrite H5...
      rewrite <- H13...
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
  Qed.
   
  Theorem FocusingRightQU : forall n D B C FX th,
      (seqN th n B D (>> makeRuleQ C Right FX)) ->
     (exists m N, n = S m /\ Permutation D ((u|t_quant C FX|)::N) /\
                seqN th m B N  (>> QDefs (rulesQ C) Right FX)) \/
    (exists m , n = S m  /\ In (u| t_quant C FX |) (second B) /\
                seqN th m B D (>> QDefs (rulesQ C) Right FX)).
  Proof with sauto.
      intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
  Qed.      
  
    Theorem FocusingLeftQU : forall n D B C FX th,
      (seqN th n B D (>> makeRuleQ C Left FX)) ->
     (exists m N, n = S m /\ Permutation D ((d|t_quant C FX|)::N) /\
                seqN th m B N  (>> QDefs (rulesQ C) Left FX)) \/
    (exists m, n = S m  /\ In (d| t_quant C FX |) (second B) /\
                seqN th m B D (>> QDefs (rulesQ C) Left FX)).
  Proof with sauto.
        intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
Qed.
   
  Theorem FocusingRightMU : forall n a D B C A th,
      (seqN th n B D (>> makeRuleM C Right A a)) ->
     (exists m N, n = S m /\ Permutation D ((u|t_ucon C A|)::N) /\
                seqN th m B N  (>> MDRulesDefs (rulesU C) Right A a)) \/
    (exists m , n = S m  /\ In (u| t_ucon C A |) (second B) /\
                seqN th m B D (>> MDRulesDefs (rulesU C) Right A a)).
  Proof with sauto.
        intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
Qed.
   
  Theorem FocusingLeftMU : forall n a D B C A th,
      (seqN th n B D (>> makeRuleM C Left A a)) ->
     (exists m N, n = S m /\ Permutation D ((d|t_ucon C A|)::N) /\
                seqN th m B N  (>> MDRulesDefs (rulesU C) Left A a)) \/
    (exists m , n = S m  /\ In (d| t_ucon C A |) (second B) /\
                seqN th m B D (>> MDRulesDefs (rulesU C) Left A a)).
  Proof with sauto.
        intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
   Qed. 
   
    
  Theorem FocusingRightCteU : forall n B D C th,
      (seqN th n B D (>> makeRuleConstant C Right)) ->
 (exists m N, n = S m /\ Permutation D ((u|t_cons C|)::N) /\
                seqN th m B N  (>> CteRulesDefs (rulesCte C) Right)) \/
    (exists m, n = S m  /\ In (u| t_cons C |) (second B) /\
                seqN th m B D  (>> CteRulesDefs (rulesCte C) Right) ). 
  Proof with sauto.
        intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
Qed.
   
   Theorem FocusingLeftCteU : forall n B D C th,
      (seqN th n B D (>> makeRuleConstant C Left)) ->
 (exists m N, n = S m /\ Permutation D ((d|t_cons C|)::N) /\
                seqN th m B N  (>> CteRulesDefs (rulesCte C) Left)) \/
    (exists m, n = S m  /\ In (d| t_cons C |) (second B) /\
                seqN th m B D  (>> CteRulesDefs (rulesCte C) Left) ). 
  Proof with sauto.
        intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H9... 
      left.
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H10.
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H13...
      CleanContext.
      
      
      rewrite H2...
      LLExact H10.
      inversion H6.
    * inversion H1.
 Qed.
    
  Theorem FocusingPOSU : forall n a D B OO th,
   seqN th n B D (>> POS OO a) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((d| OO |)::N) /\
                seqN th m (B++[(a, d| OO |)]) N  (> [] )) \/
    (exists m, n = S (S (S m))  /\ In (d| OO |) (second B) /\

                seqN th m (B++[(a, d| OO |)]) D  (> [] )).            
   Proof with sauto.
         intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H10...
      inversion H12...
       inversion H9... 
      left.
     
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H13.
      rewrite H0...
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H16...
      
      LLExact H13.
      rewrite H0...
      inversion H8.
      solveF.
    * inversion H1.
Qed.
   Theorem FocusingNEGU : forall n a D B OO th,
   seqN th n B D (>> NEG OO a) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((u| OO |)::N) /\
                seqN th m (B++[(a, u| OO |)]) N  (> [] )) \/
    (exists m, n = S (S (S m))  /\ In (u| OO |) (second B) /\
                seqN th m (B++[(a, u| OO |)]) D  (> [] )).            
   Proof with sauto.
         intros.
    inversion H...
  assert(Permutation B D0).
      apply simplUnb in H5...
    * CleanContext.
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
      inversion H10...
      inversion H12...
       inversion H9... 
      left.
     
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H13.
      rewrite H0...
      right.
      exists n0.
      split;auto.
      split;auto.
      eapply @InSecondInv with (i:=i)...
      rewrite H5...
      rewrite <- H16...
      
      LLExact H13.
      rewrite H0...
      inversion H8.
      solveF.
    * inversion H1.
Qed.
 
  Theorem AppPARTENSORRightC :
    forall n A B D G th,
    (seqN th n G D (>> RulesDefsC PARTENSOR Right A B)) ->
      exists m , n = S(S(S m))  /\
                 (seqN th m G (u| A |::D) (> []) ) /\
                 (seqN th m G (u| B |::D) (> []) ) .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    eexists n0.
    split;eauto.
  Qed.


  Theorem AppPARTENSORRightI :
    forall n a A B D G th,
    (seqN th n G D (>> RulesDefsI (i:=a) PARTENSOR Right A B)) ->
      exists m , n = S(S(S m))  /\
                 (seqN th m G (u| A |::D) (> []) ) /\
                 (seqN th m G (u| A |::D) (> []) ) .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    eexists.
    split;eauto.
  Qed.


  Theorem AppPARTENSORLeftC:
    forall n A B D G th,
    (seqN th n G D (>> RulesDefsC  PARTENSOR Left A B)) ->
     ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| A |::D) (> []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| B |::D) (> []) ))              .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    left.
    eexists.
    split;eauto.
    right.
    eexists.
    split;eauto.
  Qed.

  Theorem AppPARTENSORLeftI:
    forall n a A B D G th,
    (seqN th n G D (>> RulesDefsI (i:=a) PARTENSOR Left A B)) ->
     ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| A |::D) (> []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| B |::D) (> []) ))              .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    left.
    eexists.
    split;eauto.
    right.
    eexists.
    split;eauto.
  Qed.
  
 
   Theorem AppTENSORPARRightC :
    forall n A B D G th,
      (seqN th n G D (>> RulesDefsC TENSORPAR Right A B)) ->
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (u| A |::D) (> []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (u| B |::D) (> []) ))              .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    left.
    eexists.
    split;eauto.
    right.
    eexists.
    split;eauto.
  Qed.
  
   Theorem AppTENSORPARRightI :
    forall n A a B D G th,
      (seqN th n G D (>> RulesDefsI (i:=a) TENSORPAR Right A B)) ->
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (u| A |::D) (> []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (u| B |::D) (> []) ))              .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
    left.
    eexists.
    split;eauto.
    right.
    eexists.
    split;eauto.
  Qed.
   

  Theorem AppTENSORPARLeftC :
    forall n A B D G th,
      (seqN th n G D (>> RulesDefsC TENSORPAR Left A B)) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m G (d| A|::D) (> []) ) /\
                   (seqN th m G (d| B|::D) (> []) )) .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll.
    eexists.
    split;eauto.
  Qed.


  Theorem AppTENSORPARLeftI :
    forall n a A B D G th,
      (seqN th n G D (>> RulesDefsI (i:=a) TENSORPAR Left A B)) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m G (d| A|::D) (> []) ) /\
                   (seqN th m G (d| B|::D) (> []) )) .
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll.
    eexists.
    split;eauto.
  Qed.

  Theorem AppTENSORPAREXCHRightC :
    forall n A B D G th,
      (seqN th n G D (>> RulesDefsC TENSORPAREXCH Right A B)) ->
      exists m , n = S(S(S(S m)))  /\
                 seqN th m G (u| B | :: d| A | ::D) (> []).
  Proof with solveF.
    intros.
    simpl in H.
    FLLInversionAll.
    eexists.
    split;eauto.
  Qed.

  Theorem AppTENSORPAREXCHRightI n a A B D G th:
    m4 a = true -> mt a = true ->
      (seqN th n G D (>> RulesDefsI (i:=a) TENSORPAREXCH Right A B)) ->
      exists m C4 CN, n - length C4 -2 = (S(S(S m))) /\ n >= length C4 + 1 /\ 
      Permutation G (C4++CN) /\ D = [] /\ SetK4 a C4 /\
                 seqN th m C4 (u| B | :: d| A | ::D) (> []).
  Proof with sauto.
    intros Fa  Ta Hyp.
    simpl in Hyp.
    inversion Hyp...
    inversion H0.
    SLSolve.
    apply InvSubExpPhaseUK4 in H5...
    rewrite SetTPlusT in H7...
    FLLInversionAll...
    exists n.
    exists x.
    exists x0.
    split;auto...
    lia.
    eapply @SetTK4Closure with (i:=a)...
    apply allU.
  Qed.
    
Theorem AppTENSORPAREXCHLeftC :
    forall n A B D G th,
  (seqN th n G D (>> RulesDefsC TENSORPAREXCH Left A B)) ->
      exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( seqN th m G (u| A |::M) (> [])) /\
                  ( seqN th m G (d| B |::N) (> [])).
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
     assert(Permutation G D0).
      apply simplUnb in H5...
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
 
    eexists.
    eexists M.
    eexists N.
    split;eauto.
    split;eauto.
    split;auto.
    LLExact H13.
    LLExact H14.
   Qed. 
   
Theorem AppTENSORPAREXCHLeftI :
    forall n a A B D G th,
  (seqN th n G D (>> RulesDefsI (i:=a) TENSORPAREXCH Left A B)) ->
      exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( seqN th m G (u| A |::M) (> [])) /\
                  ( seqN th m G (d| B |::N) (> [])).
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll...
     assert(Permutation G D0).
      apply simplUnb in H5...
      rewrite Permutation_app_comm in H5.
      apply simplUnb in H5...
 
    eexists.
    eexists M.
    eexists N.
    split;eauto.
    split;eauto.
    split;auto.
    LLExact H13.
    LLExact H14.
   Qed. 
   
  Theorem AppQUESTBANGRight :
    forall n a A D G th,
    m4 a = true -> mt a = true ->
    seqN th n G D (>> MDRulesDefs QUESTBANG Right A a) ->
     exists m C4 CN, n - length C4 -1 = ((S(S m))) /\ n >= length C4 + 1 /\ 
       Permutation G (C4++CN) /\ D = [] /\ SetK4 a C4 /\
                  ( seqN th m C4 (u| A |::D) (> [])).
  Proof with sauto.
    intros.
    simpl in H1.
     inversion H1...
    inversion H3. SLSolve.
    apply InvSubExpPhaseUK4 in H8...
    rewrite SetTPlusT in H10...
    FLLInversionAll...
    exists n.
    exists x.
    exists x0.
    split;auto...
    lia.
    eapply @SetTK4Closure with (i:=a)...
    apply allU.
  Qed.
    
    
  
 
  Theorem AppALLSOMERight :
    forall n FX D G th,
      seqN th n G D (>> QDefs ALLSOME Right FX) ->
      exists m, n =  S(S(S m))  /\
             forall x, proper x -> 
                  ( seqN th m G (u| FX x |::D) (> [])).
  Proof with sauto.
    intros.
    simpl in H.
    FLLInversionAll.
    destruct n.
    specialize (H7 (Var 0) (proper_VAR _ 0)).
    inversion H7.
    eexists.
    split;auto;intros.
    apply H7 in H...
    invTri H...
  Qed.

  Theorem AppALLSOMELeft :
    forall n FX D G th,
      seqN th n G D (>> QDefs ALLSOME Left FX) ->
      exists m t ,n =  S(S(S m))  /\
                    proper t /\
                    ( seqN th m  G (d| FX t |::D) (> [])).
  Proof with solveF.
    intros.
    simpl in H.
    FLLInversionAll.
    eexists.
    eexists;eauto.
  Qed.
 

  Theorem AppSOMEALLLeft :
    forall n FX G D th,
      seqN th n G D (>> QDefs SOMEALL Left FX) ->
      exists m  ,  n =  S(S(S m))  /\
                   forall t, proper t -> 
                             ( seqN th m G (d| FX t|::D)  (> [])).
  Proof with solveF.
    intros.
    simpl in H.
    FLLInversionAll.
    destruct n.
    specialize(H7 (Var 0) (proper_VAR _ 0)). inversion H7.
    eexists;eauto.
    split;auto;intros.
    apply H7 in H...
    FLLInversionAll.
    LLExact H9.
  Qed.

  Theorem AppSOMEALLRight :
    forall n FX D G th,
      seqN th n G D (>> QDefs SOMEALL Right FX) ->
      exists m  t ,  n =  S(S(S m))  /\
                     proper t /\
                     ( seqN th m G (u| FX t |::D) (> [])).
  Proof with solveF.
    intros.
    simpl in H.
    FLLInversionAll.
    exists n0. exists t.
    split;eauto.
  Qed.

   
 Lemma OLTheoryC_HasPos : hasPos OLTheoryC loc.
 Proof. unfold hasPos. 
        intros.
        apply ooth_posC;auto;SLSolve. 
 Qed. 

 Lemma OLTheoryC_HasNeg : hasNeg OLTheoryC loc.
 Proof. unfold hasNeg. 
        intros.
        apply ooth_negC;auto;SLSolve. 
 Qed.  
 
 Lemma OLTheoryI_HasPos i a: m4 a = true -> mt a = true ->
 hasPos (OLTheoryI (i:=i) (a:=a) ) a.
 Proof. unfold hasPos. 
        intros.
        apply ooth_posI;auto;SLSolve. 
 Qed. 

 Lemma OLTheoryI_HasNeg i a: hasNeg (OLTheoryI (i:=i) (a:=a) ) loc.
 Proof. unfold hasNeg. 
        intros.
        apply ooth_negI;auto;SLSolve. 
 Qed.
 
End Bipoles.

 Global Hint Resolve OLTheoryC_HasPos OLTheoryC_HasNeg : core.  
 Global Hint Resolve OLTheoryI_HasPos OLTheoryI_HasNeg : core. 
        

