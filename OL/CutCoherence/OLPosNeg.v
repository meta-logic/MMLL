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
  Definition POS F a := MAnd (perp (down F)) (Quest a (atom (down F))).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F a := MAnd (perp (up F)) (Quest a (atom (up F))).

Definition hasPos th a:= (forall OO: uexp, isOLFormula OO -> th (POS OO a)).
Definition hasNeg th a:= (forall OO: uexp, isOLFormula OO -> th (NEG OO a)).

Lemma PosF : forall a (th : oo -> Prop) F D M, 
isOLFormula F -> hasPos th a ->
seq th ((CEncode a [d| F |])++D ) (M) (UP []) -> 
seq th D (d| F | :: M) (UP []).
Proof with sauto.
 intros. 
 TFocus (POS F a).
 inversion H1...
  LLTensor [d| F |] M.
 Qed.    

Lemma PosFS : 
forall a b (th : oo -> Prop) F D M, 
isOLFormula F -> hasPos th a -> mt b = true ->
seq th ((a, d| F |)::D ) M (UP []) -> 
seq th ((b, d| F |)::D ) M (UP []).
Proof with sauto.
 intros. 
 TFocus (POS F a).
 inversion H2...
  LLTensor (@nil oo) M.
  solveLL.
  apply weakening...
  apply allU.
 Qed.
 
 
Lemma NegF : forall a (th : oo -> Prop) F D M, 
isOLFormula F -> hasNeg th a ->
seq th ((CEncode a [u| F |])++D ) (M) (UP []) -> 
seq th D (u| F | :: M) (UP []).
Proof with sauto.
 intros. 
 TFocus (NEG F a).
 inversion H1.
  LLTensor [u| F |] M.
 Qed. 
 
Lemma NwgFS : 
forall a b (th : oo -> Prop) F D M, 
isOLFormula F -> hasNeg th a -> mt b = true ->
seq th ((a, u| F |)::D ) M (UP []) -> 
seq th ((b, u| F |)::D ) M (UP []).
Proof with sauto.
 intros. 
 TFocus (NEG F a).
 inversion H2...
  LLTensor (@nil oo) M.
  solveLL.
  apply weakening...
  apply allU.
 Qed.

Lemma PosSetP L : forall a (th : oo -> Prop) D M, 
isOLFormulaL L -> hasPos th a ->
seq th (CEncode a (LEncode L)++D ) (M) (UP []) -> 
seq th D (M++LEncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  TFocus (POS a a0)...
  inversion H1...
  LLTensor [d| a |] (M ++ LEncode L)...
  solveLL.
    eapply IHL with (a:=a0)...
    LLExact H0.
 Qed.    

Lemma NegSetP L : forall a (th : oo -> Prop) D M, 
isOLFormulaL L -> hasNeg th a ->
seq th (CEncode a (REncode L)++D ) (M) (UP []) -> 
seq th D (M++REncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  TFocus (NEG a a0).
  inversion H1.
  LLTensor [u| a |] (M ++ REncode L)...
  solveLL.
    eapply IHL with (a:=a0)...
    LLExact H0.
 Qed.
 
Theorem PosNegSetT : forall a b (th:oo->Prop) D L1 L2,  
isOLFormulaL L1 -> isOLFormulaL L2 ->
hasNeg th b ->
hasPos th a ->
seq th (D ++ CEncode a (LEncode L1) ++ CEncode b (REncode L2)) [] (UP []) ->
seq th D (LEncode L1++REncode L2) (UP []).
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
seq th (CEncode a L1++CEncode a L2 ++D) [] (UP []) ->
seq th D (L1++L2) (UP []).
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
seq th (CEncode a L++D) [] (UP []) ->
seq th D (L) (UP []).
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

Lemma WeakPosNeg: forall (th:oo->Prop) a D M N,  
hasPos th a -> hasNeg th a -> 
IsPositiveAtomFormulaL N -> 
seq th D M (UP []) ->
seq th D (M++N) (UP []).
Proof with sauto.
  intros.
  specialize (posDestruct' H) as HC...
  rewrite H1.
  rewrite app_assoc.
  apply NegSetP with (a:=a)...
  rewrite H1 in H...
  apply PositiveAtomREOLFormula.
  OLSolve.
  apply weakeningGen...
  apply PosSetP with (a:=a)...
  rewrite H1 in H...
  apply PositiveAtomLEOLFormula.
  OLSolve.
  apply weakeningGen...
Qed.  
 
  Lemma WeakPosNegAll: forall (th:oo->Prop) a D M,  
hasPos th a -> hasNeg th a -> 
IsPositiveAtomFormulaL M -> 
seq th D [] (UP []) ->
seq th D M (UP []).
Proof with sauto.
  intros.
  rewrite <- (app_nil_l M).
  eapply WeakPosNeg with (a:=a)...
  Qed.

Lemma LinearToClassic2 a b (th:oo->Prop) M MR ML N L :
hasPos th a -> hasNeg th b -> 
IsPositiveAtomFormulaL M ->
Permutation M (LEncode ML++REncode MR ) ->
seq th (CEncode a (LEncode ML) ++ CEncode b (REncode MR)++L) N (UP [])  
 -> seq th L (M ++ N) (UP []) .
Proof with sauto.
   intros Hpos Hneg isFM HP Hyp.
   eapply exchangeLC with (LC:=(N++LEncode ML) ++ REncode MR).
   rewrite HP...
   rewrite HP in isFM...
   apply NegSetP with (a:=b)...
   apply PositiveAtomREOLFormula.
   OLSolve.
   apply PosSetP with (a:=a)...
   apply PositiveAtomLEOLFormula.
   OLSolve.
 Qed.              
  
Lemma LinearToClassicAll a b (th:oo->Prop)  M MR ML N NR NL L :
hasPos th a -> hasNeg th b ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
Permutation M (LEncode ML++REncode MR ) ->
Permutation N (LEncode NL++REncode NR) ->

seq th(CEncode a (LEncode (ML++NL)) ++ CEncode b (REncode (MR++NR))++L) [] (UP [])  
 -> seq th L (M ++ N) (UP []) .
Proof with sauto.
   intros Hpos Hneg isFM isFN HPM HPN Hyp.
   eapply exchangeLC with (LC:=LEncode (ML ++ NL) ++REncode (MR ++ NR)).
   rewrite !LEncodeApp.
   rewrite !REncodeApp.
   rewrite HPM, HPN...
   rewrite HPM in isFM...
   rewrite HPN in isFN...
   apply NegSetP with (a:=b)...
   apply PositiveAtomREOLFormula.
   rewrite REncodeApp.
   OLSolve;OLSolve.
   rewrite <- (app_nil_l  (LEncode (ML ++ NL))).
   apply PosSetP with (a:=a)...
   apply PositiveAtomLEOLFormula.
   rewrite LEncodeApp. 
   OLSolve;OLSolve.
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

