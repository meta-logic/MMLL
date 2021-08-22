Require Export MMLL.OL.CutCoherence.OLTactics.
Require Export MMLL.OL.CutCoherence.OLDefinitions.

Export ListNotations.
Export LLNotations.

Set Implicit Arguments.
  

(** ** Rules of the encoded proof system *)
Section OLPOSNEG.
Context `{OLS : OLSyntax}.
Context {SI : Signature}.
Context {USI : UnbSignature}.


 (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS F a := (perp (down F)) ** (a ? (atom (down F))).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F a := (perp (up F)) ** (a ? atom (up F)).

Definition hasPos th a:= (forall OO: uexp, isOLFormula OO -> th (POS OO a)).
Definition hasNeg th a:= (forall OO: uexp, isOLFormula OO -> th (NEG OO a)).

Lemma PosF : forall a (th : oo -> Prop) F D M, 
isOLFormula F -> hasPos th a ->
seq th ((CEncode a [d| F |])++D ) (M) (> []) -> 
seq th D (d| F | :: M) (> []).
Proof with sauto.
 intros. 
 decide3 (POS F a)...
  tensor [d| F |] M.
 Qed.    

Lemma NegF : forall a (th : oo -> Prop) F D M, 
isOLFormula F -> hasNeg th a ->
seq th ((CEncode a [u| F |])++D ) (M) (> []) -> 
seq th D (u| F | :: M) (> []).
Proof with sauto.
 intros. 
 decide3 (NEG F a)...
  tensor [u| F |] M.
 Qed. 
 

Lemma PosSetP L : forall a (th : oo -> Prop) D M, 
isOLFormulaL L -> hasPos th a ->
seq th (CEncode a (LEncode L)++D ) (M) (> []) -> 
seq th D (M++LEncode L) (> []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  decide3 (POS a a0)...
  tensor [d| a |] (M ++ LEncode L)...
    eapply IHL with (a:=a0)...
    LLExact H0.
 Qed.    

Lemma NegSetP L : forall a (th : oo -> Prop) D M, 
isOLFormulaL L -> hasNeg th a ->
seq th (CEncode a (REncode L)++D ) (M) (> []) -> 
seq th D (M++REncode L) (> []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  decide3 (NEG a a0)...
  tensor [u| a |] (M ++ REncode L)...
    eapply IHL with (a:=a0)...
    LLExact H0.
 Qed.
 
Theorem PosNegSetT : forall a b (th:oo->Prop) D L1 L2,  
isOLFormulaL L1 -> isOLFormulaL L2 ->
hasNeg th b ->
hasPos th a ->
seq th (D ++ CEncode a (LEncode L1) ++ CEncode b (REncode L2)) [] (> []) ->
seq th D (LEncode L1++REncode L2) (> []).
Proof with sauto.
  intros.
  apply NegSetP with (a:=b)...
  rewrite <- (app_nil_l (LEncode L1)).
  apply PosSetP with (a:=a)...
  LLExact H1. 
Qed.  
 

Lemma PosNegSetT' : forall (th:oo->Prop) a D L1 L2,  
hasNeg th a -> hasPos th a ->
IsPositiveAtomFormulaL L1 -> IsPositiveAtomFormulaL L2 ->
seq th (CEncode a L1++CEncode a L2 ++D) [] (> []) ->
seq th D (L1++L2) (> []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL L1) by auto.
  assert(IsPositiveAtomFormulaL L2) by auto.
  apply posDestruct' in H2.
  apply posDestruct' in H3...
  assert(isOLFormulaL x1).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x2).
  apply PositiveAtomREOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve. 
 
  rewrite H2.
   
  LLPerm((L2++LEncode x1) ++ REncode x2).
  apply NegSetP with (a:=a)...
  apply PosSetP with (a:=a)...
  
  rewrite H3.
  apply NegSetP with (a:=a)...
  rewrite <- (app_nil_l (LEncode x)).
  apply PosSetP with (a:=a)...
  eapply exchangeCC.
  2:{ exact H1. }
  srewrite H2.
  srewrite H3.
  OLfold.
  rewrite !CEncodeApp.
  rewrite !app_assoc. perm.
Qed.  

Lemma LinearToClassic: forall (th:oo->Prop) a D L,  
hasPos th a -> hasNeg th a -> 
IsPositiveAtomFormulaL L -> 
seq th (CEncode a L++D) [] (> []) ->
seq th D (L) (> []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL L) by auto.
  apply posDestruct' in H1...
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve.
 
  rewrite H1.
  apply PosNegSetT' with (a:=a)...
  OLSolve.
  OLSolve.
  eapply exchangeCC.
  2:{ exact H0. }
  srewrite H1.
  OLfold.
  rewrite !CEncodeApp.
  perm.
Qed.

End OLPOSNEG.

Tactic Notation "PosNeg"  constr(j) := 
  match goal with
     | [ |- seq _ _  (u| _ | :: _) _ ] =>  eapply NegF with (a:=j);auto
     | [ |- seq _ _  (d| _ | :: _) _ ] =>  eapply PosF with (a:=j);auto
end.

Tactic Notation "PosNegAll"  constr(j) := 
  match goal with
     | [ |- seq _ _ _ _ ] =>  eapply LinearToClassic with (a:=j);auto
     | [ |- seq _ _ _ _ ] =>  eapply LinearToClassic with (a:=j);auto
end.


Tactic Notation "PosNegAll"  constr(i) constr(j) := 
  match goal with
     | [ |- seq _ _ _ _ ] =>  eapply PosNegSetT with (a:=i) (b:=j);auto
     | [ |- seq _ _ _ _ ] =>  eapply PosNegSetT with (a:=i) (b:=j);auto
end.
