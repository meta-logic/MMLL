Require Export MMLL.SL.Syntax.

Section SubExpSets.
  Context `{SI : Signature}.
  Context `{OLS : OLSig}.
 
 Definition SetX  (x:  subexp -> bool) (b:bool) (K : list TypedFormula):= Forall (fun k => x (fst k) = b) K.
 
 Definition LtX  i (K : list TypedFormula) := Forall (fun k => lt i (fst k)) K.
  
 Global Instance perm_SetX A b :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (SetX A b).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetX.
      rewrite <- H;auto.
    Qed.

Global Instance perm_LtX a :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (LtX a).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold LtX.
      rewrite <- H;auto.
    Qed.


  Definition Loc (L:list TypedFormula):= 
        map (fun x => (loc,(snd x))) L.
  Global Instance perm_Loc :
      Proper (@Permutation TypedFormula ==> @Permutation TypedFormula)
             (Loc ).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      unfold Loc.
      rewrite <- H;auto.
    Qed.
    
  Definition PlusT (L:list TypedFormula):=   
        map (fun x => (plust (fst x),snd x) ) L.
  Global Instance perm_PlusT :
      Proper (@Permutation TypedFormula ==> @Permutation TypedFormula)
             (PlusT ).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      unfold PlusT.
      rewrite <- H;auto.
    Qed.
  
   Fixpoint getU  (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then (x,F) :: (getU l0) else getU l0
  end.
  
 Fixpoint getL (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then getL l0 else (x,F) :: (getL l0) 
  end.
   
End SubExpSets.

 Global Hint Unfold SetX LtX PlusT Loc first second: core.  

(* Ltac sfold := 
repeat
match goal with
 | [  |- context[map (fun x => (loc,_)) ?K]] => change (map (fun x => (loc,_)) K) with (Loc K) 
 | [  |- context[map (fun x => (plust _,_)) ?K]] => change (map (fun x => (plust _,_)) K) with (PlusT K)
  | [  |- context[map snd ?L] ] => change (map snd L) with (second L)
 | [ H : context[map snd ?L] |- _ ] => fold (second L) in H
  
 | [ H : context[map (fun x => (loc,_)) ?K] |- _ ] => fold (Loc K) in H  
 | [ H : context[map (fun x => (plust _,_)) ?K] |- _ ] => fold (PlusT K) in H 
(*  | [ H : context[Forall isFormula ?L] |- _ ] => fold (isFormulaL L) in H     *)            
end. *)
 
 
 
Tactic Notation "srewrite" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => try rewrite H
                     
end.

Tactic Notation "srewrite_reverse" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => symmetry in H;try rewrite H
                     
end.


Tactic Notation "srewrite" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => try rewrite H1 in H2
                     
end.

Tactic Notation "srewrite_reverse" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => symmetry in H1; try rewrite H1 in H2
                     
end.

 Ltac simplSignature1 := 
  repeat 
    multimatch goal with
  (* Basic simplifcation *)
  | [  |- context[_ []] ] => simpl
  | [ H: context[_ []]  |- _ ] => simpl in H
 
 | [ H: context[if u loc then _ else _] |- _ ] => rewrite locu in H
 | [ H: context[if mt loc then _ else _] |- _ ] => rewrite locT in H
 | [ H: context[if md loc then _ else _] |- _ ] => rewrite locD in H
 | [ H: context[if m4 loc then _ else _] |- _ ] => rewrite loc4 in H
 | [ H: context[if mk loc then _ else _] |- _ ] => rewrite locK in H
 | [ |- context[if u loc then _ else _]  ] => rewrite locu 
 | [ |- context[if mt loc then _ else _] ] => rewrite locT 
 | [ |- context[if md loc then _ else _] ] => rewrite locD 
 | [ |- context[if m4 loc then _ else _] ] => rewrite loc4 
 | [ |- context[if mk loc then _ else _] ] => rewrite locK 

  | [ H1: u (fst ?F) = _, H2: context[_(?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; try rewrite H1 in H2 
  | [ H: u (fst ?F) = _ |- context[_ (?F :: _)] ] => 
     destruct F;simpl;simpl in H; try rewrite H 
 | [ H1: ?s ?a = _, H2: context[if ?s ?a then _ else _] |- _ ] => rewrite H1 in H2 
 | [ H: ?s ?a = _|- context[if ?s ?a then _ else _] ] => rewrite H 

(* About second *)
 | [ H: context[second(_++_)] |- _ ] => rewrite secondApp in H 
 | [ |- context[second(_++_)] ] => rewrite secondApp
 
 | [  |- context[_ (_::_)] ] => simpl
  | [ H: context[_ (_::_)] |- _ ] => simpl in H 

  end.

 
 Ltac solveSignature1 := try
  match goal with
  | [ H1: UnbNoDSignature, H2: md _ = true |- _ ] => rewrite allNoD in H2;discriminate H2 
  | [ H: UnbSignature |- u ?i = true ] => apply allU 
  | [ H: md ?i = true |- ?i <> loc ] => apply locNoD;auto 
  | [ H: m4 ?i = true |- ?i <> loc ] => apply locNo4;auto 
  | [ H: mt ?i = false |- ?i <> loc ] => apply locTDiff;auto 
  | [ H: u ?i = false |- ?i <> loc ] => apply locUDiff;auto 

  | [ |- lt ?i ?i] => apply @PreOrder_Reflexive; exact lt_pre
  | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = true ] => apply locK 
  | [ |- md loc = false ] => apply locD
  
  | [ |- mt (plust _) = true ] => apply T_in_plust
  | [ |- subexp ] => exact loc
    
  | [H: u loc = false |- _] => rewrite locu in H; discriminate H   
  | [H: mk loc = false |- _] => rewrite locK in H; discriminate H  
  | [H: mt loc = false |- _] => rewrite locT in H; discriminate H  
  | [H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H  
  | [H: md loc = true |- _] => rewrite locD in H; discriminate H  

  | [H1: ?a <> loc, H2: lt ?a loc |- _] => apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
  | [H1: ?a <> loc, H2: lt loc ?a |- _] => apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction
    
   | [H: SetX ?a ?b (?F::?K) |- ?a (fst ?F) = ?b] => inversion H;subst;auto
   | [H: SetX ?a ?b ((?s, _)::?K) |- ?a ?s = ?b] => inversion H;subst;auto
  
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
   
  end.
  
 Ltac solveLocation :=simplSignature1; try solve [solveSignature1]; autounfold in *;solveForall.
 

Section Properties.
  Context `{SI : Signature}.
  Context `{OLS : OLSig}.
       
  Lemma locSetK1 sub a b F: sub a = b -> SetX sub b [(a, F)].
  Proof with solveLocation.
  constructor... 
  Qed.

   
(*   Lemma locSetK2 i F: i <> loc -> ~ SetK i [(loc, F)]. *)
  
  Lemma locSetK4 F:  ~ SetX m4 true [(loc, F)].
  Proof with sauto.
  intro.
  inversion H...
  solveLocation.
  Qed.
 
  Lemma locSetD F:  ~ SetX md true [(loc, F)].
  Proof with sauto.
  intro.
  inversion H...
  solveLocation.
  Qed.
  
  Lemma locSetU F : SetX u true [(loc, F)].
  Proof.
  solveLocation.
  simpl. solveSubExp. 
  Qed.
 
 (* Local Hint Resolve locSetX:core.
 *)
  
  Lemma locSetT F : SetX mt true [(loc, F)].
  Proof.
  unfold SetX.
  constructor;auto. 
  simpl. solveSubExp. 
  Qed.
  
  Lemma locApp K1 K2: Loc (K1 ++ K2) = Loc K1 ++ Loc K2.
  Proof.
  apply map_app.
   Qed.
 
  Lemma PlusTApp K1 K2: PlusT (K1 ++ K2) = PlusT K1 ++ PlusT K2.
  Proof.
  apply map_app.
   Qed.
 
 Lemma locApp' K1 K2 : Permutation (Loc (K1 ++ K2)) (Loc K1 ++ Loc K2).
  Proof.
  solveLocation.
  rewrite map_app;auto.
  Qed.
 
 Lemma PlusTApp' K1 K2: Permutation (PlusT (K1 ++ K2)) (PlusT K1 ++ PlusT K2).
  Proof.
  unfold PlusT.
  rewrite map_app;auto.
   Qed.
   
   Lemma SetU_then_empty K : SetX u true K -> getL K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 
  
    
   Lemma SetL_then_empty K : SetX u false K -> getU K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 

  
  Lemma MapPlusT_fixpoint : forall C , PlusT (PlusT C) = (PlusT C).
  Proof with subst;auto.
  induction C;simpl;intros;auto.
  rewrite plust_plust_fixpoint...
  rewrite IHC...
  Qed.
 
     
  Lemma SetTPlusT K: SetX mt true K -> PlusT K = K.
   Proof with sauto.
   induction K;intros...
   destruct a;simpl.
   inversion H...
   apply plustpropT in H2.
   rewrite H2.
   rewrite IHK;auto.
 Qed.

   Lemma SetKRef a F: LtX a [(a, F)].
  Proof with sauto.
  apply Forall_cons... 
  apply @PreOrder_Reflexive.
  exact lt_pre.
  Qed.

   Lemma SetKTrans i a K : LtX i K -> lt a i -> LtX a K.
  Proof with sauto.
  induction K;simpl;intros...
  inversion H...
  apply Forall_cons... 
  apply @PreOrder_Transitive with (R:=lt) (y:=i);auto.
  exact lt_pre.
  apply IHK...
  Qed.

  Global Instance trans_SetK :
       Proper (lt ==> @Permutation TypedFormula ==> Basics.flip Basics.impl)
             (LtX ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl .
      intros;subst.
      rewrite H0.
      eapply (SetKTrans _ _ _ H1);auto. 
    Qed.
  
  Lemma SetKK4_then_empty' i K : SetX m4 false K -> LtX i K -> m4 i = true -> K=[].
  Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  assert(m4 p = true).
  {
  eapply m4Closure.
  exact H1. inversion H0...  }
  sauto.
  Qed.
  
  Lemma SetUL_then_empty' i K : SetX u false K -> LtX i K -> u i = true -> K=[].
  Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  assert(u p = true).
  {
  eapply uClosure.
  exact H1. inversion H0...  }
  sauto.
  Qed.
  
  
    Lemma SetTKClosure i sub K  : (forall x y : subexp,
       sub x = true -> lt x y -> sub y = true) -> sub i = true -> LtX i K -> SetX sub true K. 
  Proof with sauto.
  intros.
  induction K;intros... 
  inversion H1...
  apply Forall_cons...
  eapply H. 
  exact H0. exact H4.
  apply IHK...
  Qed.
  
(*   Check SetTKClosure _ u _ uClosure . *)
  Lemma SetUKClosure i K  : u i = true -> LtX i K -> SetX u true K. 
  Proof with sauto.
  intros.
  apply SetTKClosure with (i:=i)...
  exact uClosure.
  Qed.

 Lemma SetK4Closure i K  : m4 i = true -> LtX i K -> SetX m4 true K. 
  Proof with sauto.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply m4Closure. 
  exact H. exact H3.
  apply IHK...
  Qed.

Lemma SetDClosure i K  : md i = true -> LtX i K -> SetX md true K. 
  Proof with sauto.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply mdClosure. 
  exact H. exact H3.
  apply IHK...
  Qed.

 Lemma SetK4In sub a K: SetX sub true K -> In a K -> sub (fst a) = true.
  Proof with sauto.
  intros.
  eapply @ForallIn with (F:=a) in H...
  Qed.
 
 
  Lemma SetKK4_then_empty sub K : SetX sub true K -> SetX sub false K -> K=[].
   Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  inversion H0...
  Qed. 
  
  Theorem cxtDestruct K: Permutation K (getU K++getL K).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
  Theorem cxtDestructSecond K: Permutation (second K) (second (getU K++getL K)).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 rewrite secondApp.
 simpl.
 apply Permutation_cons_app;auto.
 rewrite <- secondApp;auto.
 Qed.

 Theorem cxtDestruct' K: exists K1 K2, Permutation K (getU K++getL K1 ++ getL K2) /\ Permutation (getL K) (getL K1 ++ getL K2).
 Proof with sauto.
 induction K...
 exists [].
 exists [].
 simpl;auto.
 destruct a as [a F].
 destruct (uDec a); simpl;
 rewrite e;simpl.
 exists x. exists x0.
 constructor;auto.
 exists ((a,F)::x).
  exists x0.
  simpl; rewrite e;simpl.
  constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
 Lemma getUPerm K1 K2 : Permutation K1 K2 -> Permutation (getU K1) (getU K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.
 
  Lemma getLPerm K1 K2 : Permutation K1 K2 -> Permutation (getL K1) (getL K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.

  Global Instance getU_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getU ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getUPerm;auto.
    Qed. 
  
    Global Instance getL_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getL ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getLPerm;auto.
    Qed. 
    
     
  Lemma getU_fixpoint K : getU(getU K) =  getU K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
    Lemma getL_fixpoint K : getL(getL K) =  getL K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.  
 
  Lemma getUgetL K : getU(getL K) =  [].
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
  Lemma getLgetU K : getL(getU K) =  [].
  Proof.
   induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
  Qed.

 
  Lemma getUApp K1 K2 : getU (K1 ++ K2) =  getU K1 ++ getU K2.
  Proof.
    induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl.
  rewrite IHK1; auto.
   Qed.
 
 
 Lemma getUApp' K1 K2 : Permutation (getU (K1 ++ K2)) (getU K1 ++ getU K2).
  Proof.
  rewrite getUApp;auto.
  Qed. 
 
 Lemma uIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *.
  rewrite e in *...  firstorder. 
  rewrite e in *...
  inversion H0...
 Qed.
 
  Lemma getLApp K1 K2 : getL (K1 ++ K2) =  getL K1 ++ getL K2.
  Proof.
  induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto.
  simpl. 
  rewrite IHK1. auto.
 Qed.
  
 Lemma getLApp' K1 K2 : Permutation (getL (K1 ++ K2)) (getL K1 ++ getL K2).
  Proof.
  rewrite getLApp;auto.
  Qed. 

Lemma lIngetL i F B :  u i = false -> In (i, F) B -> In (i, F) (getL B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
 Qed.

Lemma lIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
  inversion H0...
 Qed.


  Theorem getUtoSetU K: SetX u true (getU K).
 Proof with subst;auto.
 induction K...  
 apply Forall_nil.
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
   Theorem getLtoSetU K: SetX u true (getL K) -> getL K =[].
 Proof with sauto.
 induction K;intros. 
 * auto.
 * destruct a as [a F].
   destruct (uDec a); simpl in *;
  rewrite e in *...
  inversion H...
 Qed.
 
 
 Lemma getUPerm_SetU K X : Permutation (getU K) X -> SetX u true X.
  Proof.
  intros.
  symmetry in H.
  srewrite  H.
  apply getUtoSetU.
 Qed. 
 

 
  Theorem getLtoSetL K: SetX u false (getL K).
 Proof with subst;auto.
 induction K...
 apply Forall_nil.
 
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
  Lemma getLPerm_SetL K X : Permutation (getL K) X -> SetX u false X.
  Proof.
  intros.
  symmetry in H.
  srewrite H.
  apply getLtoSetL.
 Qed. 
 
  Theorem setUtoGetU K: SetX u true K -> getU K = K.
 Proof with subst;auto.
 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.

  Theorem setLtoGetL K: SetX u false K -> getL K = K.
 Proof with subst;auto.

 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.
 
   Lemma getUPermU K1 K2 : Permutation (getU K1) K2 -> Permutation (getU K1) (getU K2).
Proof with sauto.
 intros.
 rewrite H.
 apply getUPerm_SetU in H.
 rewrite cxtDestruct...
 rewrite (SetU_then_empty _ H)...
 rewrite setUtoGetU...
 rewrite setUtoGetU...
 Qed.
 
 Theorem Unb_Lin_Disj' K: exists K1 K2, SetX u true K1 /\ SetX u false K2 /\ Permutation K (K1++K2).
 Proof with subst;solveLocation;auto .
 induction K;auto.
 do 2 eexists [];simpl...
 destruct IHK.
 destruct H.
 decompose [and] H ;clear H.
 destruct a as [a F].
 destruct (uDec a).
 eexists ((a,F)::x).
 eexists x0.
 split... 
 eexists x.
 eexists ((a,F)::x0).
 split... 
 split...  
 rewrite H3... apply Permutation_middle.
 Qed.
 
(* Lemmata about SetK *) 
  
  (*  Lemma SetKPlusT' a K: SetK (plust a)  K -> SetX mk true K.
  Proof with sauto.
  induction K;intros;auto.

  destruct a0 as [p F].
  inversion H...
 
  apply IHK in H3;auto.
  apply Forall_cons...
  apply @PreOrder_Transitive with (R:=lt) (y:=(plust a));auto.
  exact lt_pre.
  apply plust_incL. 
  apply @PreOrder_Reflexive.
  exact lt_pre.
  Qed.
   *)
   
  Lemma SetKPlusT b K: SetX mk b K ->  SetX mk b (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.

  destruct a as [p F].
  inversion H...
  apply Forall_cons;simpl;auto.
  do 2 rewrite allK...
 apply IHK...
  Qed.
  
  
    Lemma SetK4PlusT b K: SetX m4 b K ->  SetX m4 b (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.

  destruct a as [p F].
  inversion H...
  apply Forall_cons;simpl;auto. 
  apply plust_keeping4;auto.
 apply IHK...
  Qed.

   Lemma SetK4PlusT' b K: SetX m4 b (PlusT K)  -> SetX m4 b K.
  Proof with sauto.
  induction K;simpl;intros;auto.
   apply Forall_cons...
    apply  Forall_inv in H...
    apply plust_keeping4';auto.
    apply  Forall_inv_tail in H...
  Qed.


  Lemma SetUPlusT b K: SetX u b K ->  SetX u b (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    inversion H...
    apply Forall_cons...  
    apply plust_keepingu... 
  Qed.

 Lemma PlusTSetU b K: SetX u b (PlusT K) -> SetX u b K.
  Proof with sauto.
  induction K;simpl;intros;auto.
    apply Forall_cons...
    apply  Forall_inv in H...
    apply plust_keepingu';auto.
    apply  Forall_inv_tail in H...
  Qed.
  
  Lemma SetUDec sub K :  {SetX sub true K} + {~ SetX sub true K}.
  Proof with sauto.
    induction K;simpl;auto.
    destruct IHK.
    - destruct a as [p F]... 
      destruct (subDec sub p). 
      left.  apply Forall_cons...
      right. intro.
      inversion H...
    - destruct a as [p F]. 
      destruct (subDec sub p).
      right. intro. inversion H... 
      right. intro.
      inversion H... 
 Qed.
 
 
  Lemma SetULoc K: SetX u true (Loc K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    simpl.
    apply Forall_cons...
    apply locu.  
 Qed.
 
   Lemma SetTLoc K: SetX mt true (Loc K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    simpl.
    apply Forall_cons...
    apply locT.  
 Qed.
 
  
  Lemma getLPlusT K: SetX mt true K -> getL K = getL (PlusT K).
  Proof with sauto.
  induction K. 
  * simpl;auto.
  * destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      apply IHK.
      inversion H...
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      rewrite IHK.
      apply  Forall_inv in H...
      rewrite plustpropT;auto.
      apply  Forall_inv_tail in H...
  Qed.
 
   Lemma getUPlusT K: SetX mt true K -> getU K = getU (PlusT K).
  Proof with sauto.
  induction K. 
  * simpl;auto.
  * destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      rewrite IHK.
      apply  Forall_inv in H...
      rewrite plustpropT;auto.
      apply  Forall_inv_tail in H...
 - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      apply IHK.
      inversion H...      
  Qed.
 
 Lemma getLEPlusT K: getL K = [] <-> getL (PlusT K) = [].
  Proof with sauto.
  split;intros.
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl in H. rewrite e in H.
      apply plust_keepingu in e.
      simpl.
      rewrite e...
    - simpl in H. rewrite e in H...
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
    -  simpl in H.
      apply plust_keepingu in e.
      rewrite e in H... 
Qed.

 Lemma getUEPlusT K: getU K = [] <-> getU (PlusT K) = [].
  Proof with sauto.
  split;intros.
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl in H. rewrite e in H.
      apply plust_keepingu in e.
      simpl.
      rewrite e...
    - simpl in H. rewrite e in H...
      apply plust_keepingu in e.
      simpl.
      rewrite e...
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
Qed.
    
 Lemma getUELoc K: K = [] <-> getU (Loc K) = [].
  Proof with sauto.
  split;intros.
  rewrite H. simpl;auto.
  * induction K...
    simpl in H. rewrite locu in H...
Qed.
   
  Lemma getULoc K: getU (Loc K) = Loc K.
  Proof with sauto.
  induction K;intros...
  simpl. rewrite locu...
  rewrite IHK...
Qed.

Lemma  PlusTgetU K : (PlusT (getU K)) = getU (PlusT K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    simpl.
    rewrite (plust_keepingu _ _ e).
    rewrite IHK...
  * simpl...
    rewrite (plust_keepingu _ _ e)... 
Qed.

Lemma  PlusTgetL K : (PlusT (getL K)) = getL (PlusT K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    simpl.
    rewrite (plust_keepingu _ _ e)...
  * simpl...
    rewrite (plust_keepingu _ _ e)...
    simpl.
    rewrite IHK...
Qed.

Lemma  getUPlusTgetU' K : getU (PlusT (getU K)) = PlusT (getU K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    simpl.
    rewrite (plust_keepingu _ _ e).
    rewrite IHK...
  * simpl...
Qed.

Lemma  getUPlusTgetL' K : getL (PlusT (getL K)) = PlusT (getL K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
  * simpl...
    simpl.
    rewrite (plust_keepingu _ _ e).
    rewrite IHK...    
Qed.

 Lemma getLELoc K: getL (Loc K) = [].
  Proof with sauto.
  induction K...
  destruct a as [p F].
  simpl.
  rewrite locu;auto.
 Qed. 
 
  Lemma getLgetUPlusT K: getL (PlusT (getU K)) = [].
  Proof with sauto.
  induction K... 
  destruct a as [p F].
  destruct (uDec p).
  - assert(u (plust p) = true).
    apply plust_keepingu;auto.
    simpl... 
    simpl. rewrite H;auto.
  - simpl. rewrite e;auto. 
 Qed. 
 
 Lemma getLgetUPlusT' K: SetX u true K -> getL (PlusT K) = [].
  Proof with sauto.
  induction K;intros... 
  destruct a as [p F].
  destruct (uDec p).
  - assert(u (plust p) = true).
    apply plust_keepingu;auto.
    simpl. rewrite H0.
    apply IHK.
    inversion H... 
  - inversion H... 
 Qed. 
 
  Lemma getUgetLPlusT K: getU (PlusT (getL K)) = [].
  Proof with sauto.
  
  induction K... 
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e;auto. 
  - assert(u (plust p) = false).
    apply plust_keepingu;auto. 
    simpl. rewrite e;auto.
    simpl. rewrite H;auto.
 Qed. 
 
 
  Lemma isFormulaL_getU B :  
      isFormulaL (second B) -> isFormulaL  (second (getU B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - 
      simpl in *.
      inversion H;sauto.
      apply Forall_cons;sauto.
    -
      simpl in *.
      inversion H;sauto.
  Qed.    
    
    Lemma isFormulaL_getL  B :  
      isFormulaL  (second B) -> isFormulaL  (second (getL B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - simpl in *.
      inversion H;sauto.
   -  simpl in *.
      inversion H;sauto.
      apply Forall_cons;sauto.
  Qed.
  
  Lemma isFormulaLSplitUL  B :  
      isFormulaL  (second (getU B)) ->  isFormulaL  (second (getL B)) -> isFormulaL  (second B). 
  Proof.
    intros.
    rewrite cxtDestructSecond.
    rewrite secondApp.
    apply Forall_app;auto.
  Qed.   
  
      
 Lemma isFormulaL_PlusT  B :  
      isFormulaL  (second B) -> isFormulaL  (second (PlusT B)). 
  Proof.
    induction B;simpl;unfold isFormulaL;intros;auto.
    apply Forall_cons.
    apply Forall_inv in H;auto.
    apply Forall_inv_tail in H.
    apply IHB;auto.
    Qed.
 
 Lemma isFormulaL_Loc   B :  
      isFormulaL  (second B) -> isFormulaL  (second (Loc B)). 
  Proof.
    induction B;simpl;unfold isFormulaL;intros;auto.
    constructor...
    apply Forall_inv in H;auto.
    apply Forall_inv_tail in H.
    apply IHB;auto.
    Qed.
    
     Lemma isFormulaLSecond  B D X Y:  
     Permutation (getL B) (getL D ++ X) -> 
     Permutation (getU B) (getU D ++ Y) ->
     isFormulaL  (second B) -> isFormulaL  (second D). 
  Proof.
    autounfold;unfold second;intros.
    rewrite cxtDestruct in H1.
    rewrite H in H1.
    rewrite H0 in H1.
    fold (second ((getU D ++ Y) ++ getL D ++ X)) in H1.
    repeat rewrite secondApp in H1.
    apply Forall_app in H1.
    destruct H1.
    apply Forall_app in H1.
    apply Forall_app in H2.
    sauto.
    rewrite cxtDestruct.
    fold (second (getU D ++ getL D)). 
    repeat rewrite secondApp.
    apply Forall_app;auto.
    Qed.
    
   Lemma subexpInLoc  C: forall (i:subexp) (F:oo), In (i, F) (Loc C) -> i = loc.
  Proof with subst;auto.
  induction C;intros...
  * simpl in H. contradiction.
  * simpl in H.
    destruct H.
    inversion H...
    apply IHC in H...
  Qed.
   
    Lemma subexpInMap  C: forall (i:subexp) (F:oo), In (i, F) (PlusT C) -> i = plust i.
  Proof with subst;auto.
  induction C;intros...
  * simpl in H. contradiction.
  * simpl in H.
    destruct H.
    inversion H...
    rewrite plust_plust_fixpoint;auto.
    apply IHC in H...
  Qed.
  
    Lemma SetKLoc i K  : i <> loc -> LtX i K -> In loc (first K) -> False. 
  Proof with sauto.
  induction K;simpl;intros.
  contradiction.
  destruct H1.
  * destruct a;simpl in *;subst.
    inversion H0...
    apply locAlone in H.
    apply H. left;auto.
  * apply IHK;auto.
    inversion H0...
 Qed. 

  Lemma SetK4Loc i K  : i <> loc -> SetX m4 true K -> In loc (first K) -> False. 
  Proof with sauto.
  induction K;simpl;intros.
  contradiction.
  destruct H1.
  * destruct a;simpl in *;subst.
    inversion H0... solveSubExp. 
  * apply IHK;auto.
    inversion H0...
  Qed.

  
  Lemma PlusT_fixpoint : forall C , PlusT (PlusT C) = (PlusT C).
  Proof with subst;auto.
  induction C;simpl;intros;auto.
  rewrite plust_plust_fixpoint...
  rewrite IHC...
  Qed.
  
  Lemma PlusT_fixpoint' : forall C , SetX mt true C -> (PlusT C) = C.
  Proof with sauto.
  induction C;simpl;intros;auto.
  inversion H...
  apply IHC in H3.
  rewrite H3...
  destruct a as [p F].
  simpl in *.
  rewrite plustpropT...
  Qed.
  

 Lemma getUS F t D L: getU D = (t, F)::L -> u t = true.
 Proof with sauto.
 induction D;intros...
 destruct a.
 destruct (uDec s).
 inversion H... 
 inversion H1...
 inversion H... 
 Qed.
 

  Lemma linearEmpty K : getL K = [] -> getL K = [] /\ Permutation (getU K) K /\ SetX u true K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    apply IHK in H. 
    split;sauto. 
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
Qed.

Lemma unboundedEmpty K : getU K = [] -> getU K = [] /\ Permutation (getL K) K /\ SetX u false K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
     apply IHK in H. 
    split;sauto. 
 Qed.
 
  Lemma SetK4Destruct sub b K : SetX sub b K -> SetX sub b (getU K) /\ SetX sub b (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  apply Forall_app in H...
  Qed.
  
   Lemma linearInUnb a A K : u a = false -> SetX u true K -> In (a, A) K -> False.
  Proof with sauto.
  induction K;intros...
  destruct a0.
  inversion H1...
  inversion H0...
  apply IHK...
  inversion H0... 
  Qed. 
  
  
Lemma  setUPlusTgetU K : SetX u true K -> PlusT (getU K) = PlusT K.
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  inversion H...
  simpl. rewrite H2...
  simpl...
  rewrite IHK;auto.
 Qed.

Lemma  setULocgetU K : SetX u true K -> Loc (getU K) = Loc K.
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  inversion H...
  simpl. rewrite H2...
  simpl...
  rewrite IHK;auto.
 Qed.
  
  
 Lemma SetK4LocEmpty C : LtX loc C -> SetX m4 true C -> C = []. 
 Proof with sauto.
 induction C;intros...
 inversion H...
 inversion H0...
 assert(False).
 eapply @locAlone with (a:=(fst a))...
 intro... 
 rewrite H1 in H5.
 solveSubExp.
 contradiction.
 Qed. 
 
  Lemma LtXPlusT  a K : LtX a K -> LtX (plust a) (PlusT K).
  Proof with sauto.
  induction K;simpl;intros...
  destruct a0 as [b F].
  inversion H...
  apply IHK in H3...
  apply Forall_cons...
   apply plust_mono ...
  Qed.

 Lemma InContext1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F B ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.

 Lemma InSecond1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second B) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.
  
  
  
 Lemma InContext2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F D ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.
  
  Lemma InSecond2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second D) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.  
 

  Lemma isFormulaSecond1  BD X Y B Z U:
  isFormulaL  (second (X++getU BD++Y)) -> 
  Permutation (X++getU BD++Y) (Z++B++U) ->
  isFormulaL  (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL  (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.  

 Lemma isFormulaSecond2  BD X Y B Z U:
  isFormulaL  (second (X++getL BD++Y)) -> 
  Permutation (X++getL BD++Y) (Z++B++U) ->
  isFormulaL  (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL  (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.
 


  Lemma isFormulaSecondSplit1  BD X Y B D:
  isFormulaL  (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU B) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL  (second B).
   Proof with sauto.
  intros.
   rewrite !secondApp in H.
  assert(isFormulaL  (second BD)).
  apply Forall_app in H...
  assert(isFormulaL  (second X)).
  apply Forall_app in H...
  apply Forall_app in H4...
  assert(isFormulaL  (second Y)).
  apply Forall_app in H...
  apply Forall_app in H5...
  assert(Permutation ([] ++ getU BD ++ X) ([] ++getU B ++ [])).
  sauto.
  eapply isFormulaSecond1  in H5...
  assert(Permutation ([] ++ getL BD ++ Y) ([] ++getL B ++ getL D)).
  sauto.
  eapply isFormulaSecond2  in H6...
  apply isFormulaLSplitUL...
  
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getL...
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getU...
 Qed. 
 
  Lemma isFormulaSecondSplit2  BD X Y B D:
  isFormulaL  (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU D) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL  (second D).
   Proof with sauto.
  intros.
  eapply isFormulaSecondSplit1 with (X:=X) (Y:=Y) (BD:=BD) (D:=B);auto.
  rewrite H1...
  Qed.
 
 
     Theorem destructClassicSetK4 C4 C4' CN CN': 
    SetX m4 true C4 -> SetX m4 true C4' ->
    Permutation (C4 ++ CN) (C4' ++ CN') -> 
    exists K4_1 K4_2 K4_3 N, Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
                    Permutation CN (K4_3 ++ N) /\ Permutation CN' (K4_2 ++ N). 
  Proof with subst;auto.
    intros.
    revert dependent C4'.
    revert dependent CN.
    revert dependent CN'.
    induction C4;intros.
    * 
      eexists []. 
      eexists []. 
      eexists C4'.
      eexists CN'. 
      simpl.
      split;auto.
    *
      simpl in H1.
      symmetry in H1.
      
      checkPermutationCases H1.
      - eapply IHC4 with (CN:=a::CN) (CN':=CN') in H0;
        [sauto | solveLocation | 
         rewrite H2;symmetry;rewrite <- app_comm_cons;
         apply Permutation_cons_app;auto].
         checkPermutationCases H4.
         + 
           eexists (a::x0).
           eexists x1.
           eexists x4.
           eexists x3.
           split;auto.
           rewrite <- app_comm_cons.
           apply Permutation_cons...
           split;auto.
           rewrite H5.
           rewrite H4. perm. 
         + eexists x0.
           eexists (a::x1).
           eexists x2.
           eexists x4.
           split;auto.
           apply Permutation_cons_app...
           split;auto.
           split;auto.
           rewrite H7. 
           rewrite H4. perm.
      - 
        eapply IHC4 with (CN:=CN) (CN':=x) in H0;
        [sauto | solveLocation | symmetry;auto].
        eexists x0.
        eexists (a::x1).
        eexists x2.
        eexists x3.
        split;auto.
        apply Permutation_cons_app...
        split;auto.
        split;auto.
        rewrite H2. rewrite H7.
        perm.
 Qed.       
 
  Theorem destructClassicSetK CK CK' CN CN': 
    SetX m4 false CK -> SetX m4 false CK' ->
    Permutation (CK ++ CN) (CK' ++ CN') -> 
    exists K_1 K_2 K_3 N, Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
                    Permutation CN (K_3 ++ N) /\ Permutation CN' (K_2 ++ N). 
  Proof with subst;auto.
    intros.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    induction CK;intros.
    * 
      eexists []. 
      eexists []. 
      eexists CK'.
      eexists CN'. 
      simpl.
      split;auto.
    *
      checkPermutationCases H1.
      - eapply IHCK with (CN:=a::CN) (CN':=CN') in H0;
        [sauto | solveLocation | 
         rewrite H2;symmetry;rewrite <- app_comm_cons;
         apply Permutation_cons_app;auto].
         checkPermutationCases H4.
         + 
           eexists (a::x0).
           eexists x1.
           eexists x4.
           eexists x3.
           split;auto.
           rewrite <- app_comm_cons.
           apply Permutation_cons...
           split;auto.
           rewrite H5.
           rewrite H4. perm. 
         + eexists x0.
           eexists (a::x1).
           eexists x2.
           eexists x4.
           split;auto.
           apply Permutation_cons_app...
           split;auto.
           split;auto.
           rewrite H7. 
           rewrite H4. perm.
      - 
        eapply IHCK with (CN:=CN) (CN':=x) in H0;
        [sauto | solveLocation | symmetry;auto].
        eexists x0.
        eexists (a::x1).
        eexists x2.
        eexists x3.
        split;auto.
        apply Permutation_cons_app...
        split;auto.
        split;auto.
        rewrite H2. rewrite H7.
        perm.  
 Qed.       

 Theorem destructClassicSet C4 C4' CK CK' CN CN': 
 SetX m4 true C4 -> SetX m4 true C4' -> SetX m4 false CK -> SetX m4 false CK' -> 
 Permutation (C4 ++ CK ++ CN) (C4' ++ CK' ++ CN') -> 
 (exists K_1 K_2 K_3 N, 
          Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
          Permutation (C4 ++ CN) (K_3 ++ N) /\ Permutation (C4' ++ CN') (K_2 ++ N)) /\
 (exists K4_1 K4_2 K4_3 N, 
          Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
          Permutation (CK ++ CN) (K4_3 ++ N) /\ Permutation (CK' ++ CN') (K4_2 ++ N)). 
  Proof with subst;auto.
  split;intros.
  * assert(Permutation (CK ++ (C4 ++ CN)) (CK' ++ (C4' ++ CN'))).
    rewrite Permutation_app_swap_app.
    rewrite H3. perm.
    clear H3.
    apply destructClassicSetK in H4...
  * apply destructClassicSetK4  in H3...
  Qed.
 

  Theorem destructClassicSet' C4 C4' CK CK' CN CN': 
 SetX m4 true C4 -> SetX m4 true C4' -> SetX m4 false CK -> SetX m4 false CK' -> 
 Permutation (C4 ++ CK ++ CN) (C4' ++ CK' ++ CN') -> 
 exists K_1 K_2 K_3 K4_1 K4_2 K4_3 N, 
          Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
          Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
          Permutation CN (K_3 ++ K4_3 ++ N) /\ Permutation CN' (K_2 ++ K4_2 ++ N) . 
  Proof with sauto.
  intros.
    
    revert dependent CK.
    revert dependent C4'.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    induction C4;intros...
    * 
    revert dependent C4'.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    induction CK;intros...
      eexists []. 
      eexists []. 
      eexists CK'.
      eexists []. 
      eexists []. 
      eexists C4'.
      eexists CN'...
      rewrite H3...  
      simpl in H3.
      checkPermutationCases H3.
      - rewrite H4 in H0.
        inversion H0...
        inversion H1...
      -  checkPermutationCases H4.
         rewrite <- H6 in H5.
         symmetry in H5.
         apply IHCK in H5...
         sauto...
         eexists (a :: x1).
         eexists x2.
         eexists x3.
         eexists [].
         eexists [].
         eexists x6.
         eexists x7...
         rewrite H5...
         rewrite H4.
         rewrite H8...
         inversion H1...
         rewrite H4 in H2.
         inversion H2...
         rewrite <- H6 in H5.
         symmetry in H5.
         apply IHCK in H5...
         sauto...
         eexists x1.
         eexists (a::x2).
         eexists x3.
         eexists [].
         eexists [].
         eexists x6.
         eexists x7...
         rewrite H5... 
         rewrite H4.
         rewrite H12...
         inversion H1...
    *
      simpl in H3.
      revert dependent C4'.
      revert dependent CK'.
      revert dependent CN.
      revert dependent CN'.
      induction CK;intros...
      - checkPermutationCases H3.
         symmetry in H5.
         change (C4++CN) with (C4++[]++CN) in H5.
         apply IHC4 in H5...
         sauto...
         eexists [].
         eexists [].
         eexists x2.
         eexists (a::x3).
         eexists x4.
         eexists x5.
         eexists x6...
         rewrite H6...
         rewrite H4.
         rewrite H8...
         inversion H...
         rewrite H4 in H0.
         inversion H0...
         
         checkPermutationCases H4.
         rewrite H4 in H2.
         inversion H2...
         inversion H...
         
         rewrite <- H6 in H5.
         symmetry in H5.
         change (C4++CN) with (C4++[]++CN) in H5.
         apply IHC4 in H5...
         sauto...
         eexists [].
         eexists [].
         eexists x3.
         eexists x4.
         exists (a::x5).
         eexists x6.
         eexists x7...
         rewrite H7... 
         rewrite H4.
         rewrite H12...
         inversion H...
      -  assert(Permutation  (a :: C4 ++ (a0 :: CK) ++ CN)  (a0 :: C4 ++ (a :: CK) ++ CN)) by perm.
         rewrite H4 in H3. clear H4. 
          checkPermutationCases H3.
          symmetry in H5.
            assert(Permutation (C4 ++ a :: CK ++ CN) (a ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         apply IHCK in H5... 
         rewrite H4 in H0.
         inversion H0...
         inversion H1...
         inversion H1...
         rewrite H4 in H0.
         inversion H0...
         checkPermutationCases H4.
        
         
         symmetry in H5.
         assert(Permutation (C4 ++ a :: CK ++ CN) (a ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         rewrite <- H6 in H5.
         apply IHCK in H5... 
         eexists (a0::x1).
         exists x2.
         exists x3.
         exists x4.
         exists x5.
         exists x6.
         exists x7...
         rewrite H5...
         rewrite H4.
         rewrite H8...
         inversion H1...
         rewrite H4 in H2.
         inversion H2...
         symmetry in H5.
         assert(Permutation (C4 ++ a :: CK ++ CN) (a ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         rewrite <- H6 in H5.
         apply IHCK in H5... 
         eexists x1.
         exists (a0::x2).
         exists x3.
         exists x4.
         exists x5.
         exists x6.
         exists x7...
         rewrite H5...
         rewrite H4.
         rewrite H12... inversion H1...
  Qed.
  
   Theorem destructClassicSetU' C4 C4' CK CK' CN CN': 
 SetX m4 true C4 -> SetX m4 true C4' -> SetX m4 false CK -> SetX m4 false CK' -> 
 Permutation (getU C4 ++ getU CK ++ getU CN) (getU C4' ++ getU CK' ++ getU CN') -> 
 exists K_1 K_2 K_3 K4_1 K4_2 K4_3 N, 
          Permutation (getU CK) (getU K_1 ++ getU K_2) /\ Permutation (getU CK') (getU K_1 ++ getU K_3) /\ 
          Permutation (getU C4) (getU K4_1 ++ getU K4_2) /\ Permutation (getU C4') (getU K4_1 ++ getU K4_3) /\ 
          Permutation (getU CN) (getU K_3 ++ getU K4_3 ++ getU N) /\ Permutation (getU CN') (getU K_2 ++ getU K4_2 ++ getU N) . 
  Proof with sauto.
     intros.
     apply destructClassicSet' in H3...
     eexists x.
     eexists x0.
     eexists x1.
     eexists x2.
     eexists x3.
     eexists x4.
     eexists x5.
       2:{ rewrite cxtDestruct in H. apply Forall_app in H...  }
      2:{ rewrite cxtDestruct in H0. apply Forall_app in H0... }
     2:{ rewrite cxtDestruct in H1. apply Forall_app in H1... }
    2:{ rewrite cxtDestruct in H2. apply Forall_app in H2... }
    repeat rewrite <- getUApp.
    rewrite (@setUtoGetU (x++x0)).
     rewrite (@setUtoGetU (x++x1)).
      rewrite (@setUtoGetU (x2++x3)).
       rewrite (@setUtoGetU (x2++x4)).
        rewrite (@setUtoGetU (x1++x4++x5)).
        rewrite (@setUtoGetU (x0++x3++x5))...
    
    apply getUPerm_SetU in H10...
    apply getUPerm_SetU in H8...
    apply getUPerm_SetU in H7...
    apply getUPerm_SetU in H5...
    apply getUPerm_SetU in H6...
    apply getUPerm_SetU in H4...
   Qed. 
   
     
  Theorem destructClassicSetU C4 C4' CK CK' CN CN': 
 SetX m4 true C4 -> SetX m4 true C4' -> SetX m4 false CK -> SetX m4 false CK' -> 
 Permutation (getU C4 ++ getU CK ++ getU CN) (getU C4' ++ getU CK' ++ getU CN') -> 
 (exists K_1 K_2 K_3 N, 
          Permutation (getU CK) (getU K_1 ++ getU K_2) /\ Permutation (getU CK') (getU K_1 ++ getU K_3) /\ 
          Permutation (getU C4 ++ getU CN) (getU K_3 ++ getU N) /\ Permutation (getU C4' ++ getU CN') (getU K_2 ++ getU N)) /\
 (exists K4_1 K4_2 K4_3 N, 
          Permutation (getU C4) (getU K4_1 ++ getU K4_2) /\ Permutation (getU C4') (getU K4_1 ++ getU K4_3) /\ 
          Permutation (getU CK ++ getU CN) (getU K4_3 ++ getU N) /\ Permutation (getU CK' ++ getU CN') (getU K4_2 ++ getU N)). 
  Proof with sauto.
  intros. apply destructClassicSet in H3...
  
  
  3:{ rewrite cxtDestruct in H. apply Forall_app in H... }
  3:{ rewrite cxtDestruct in H0. apply Forall_app in H0... }
  3:{ rewrite cxtDestruct in H1. apply Forall_app in H1... }
  3:{ rewrite cxtDestruct in H2. apply Forall_app in H2... }
 
  apply getUPermU  in H3.
  apply getUPermU in H10.
  setoid_rewrite <- getUApp in H8.
  apply getUPermU in H8.
  setoid_rewrite <- getUApp in H12.
  apply getUPermU in H12...

  setoid_rewrite getUApp in H3.
  setoid_rewrite getUApp in H10.
  setoid_rewrite getUApp in H8.
  setoid_rewrite getUApp in H12.
  
  exists x3. exists x4.
  exists x5. exists x6...
  
    apply getUPermU  in H5.
  apply getUPermU  in H7.
  setoid_rewrite <- getUApp in H6.
  apply getUPermU  in H6.
  setoid_rewrite <- getUApp in H9.
  apply getUPermU  in H9.
  
  setoid_rewrite getUApp in H5.
  setoid_rewrite getUApp in H6.
  setoid_rewrite getUApp in H7.
  setoid_rewrite getUApp in H9.
  
  exists x. exists x0.
  exists x1. exists x2...
  Qed.
 
  Lemma simplUnb BD B D:          
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetX u true B -> Permutation BD D.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct BD).
  rewrite H0.
  rewrite H.
  simpl. 
  rewrite <- cxtDestruct;auto.
  Qed.
  
  Lemma simplUnb' BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetX u true D -> Permutation BD B.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct BD).
  rewrite H.
  rewrite H0;sauto.
  rewrite <- cxtDestruct;auto.
  Qed.
  
 Definition SetU K := SetX  u true K. 
 Definition SetL K := SetX  u false K.
 Definition SetT K := SetX  mt true K. 
 Definition SetK K := SetX  m4 false K.
 Definition SetK4 K := SetX m4 true K.

End Properties.

 Global Hint Unfold SetU SetL SetT SetK SetK4:core. 

Global Hint Resolve SetUPlusT locSetU locSetT SetUKClosure SetK4Closure SetDClosure getUtoSetU getLtoSetL: ExBase.


Global Hint Resolve SetKPlusT SetK4PlusT SetK4PlusT' SetUPlusT PlusTSetU SetULoc SetTLoc: ExBase.

Global Hint Extern 1 (LtX ?a ?K) =>
  match goal with
  | H: LtX ?i ?K,  H1: lt ?a ?i |- _ =>  apply (SetKTrans _ _ _ H H1)
  end : core.

Global Hint Resolve SetKLoc SetK4Loc linearInUnb: ExBase.

Ltac solveLT :=  
try
 match goal with
   | [H1: ?a <> loc, H2: lt ?a loc |- _] => apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
  | [H1: ?a <> loc, H2: lt loc ?a |- _] => apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
   | [H: _ ?i (_::?K) |- LtX ?i ?K ] => inversion H;subst;intuition
   
   
   | [H: lt ?x ?y, H2: LtX ?y ?K |- LtX ?x ?K ] => rewrite H;auto
   | [H: Permutation ?K ?K', H2: LtX ?x ?K' |- LtX ?x ?K ] => rewrite H;auto
    | [H: Permutation ?K ?K', H2: LtX ?x ?K |- LtX ?x ?K' ] => rewrite <- H;auto  
 
  end;auto.

Ltac solveSE :=  
try
 match goal with
 | [H: SetK ((?s, _)::_) |- m4 ?s = false] => inversion H;subst;auto
    | [H: SetK4 ((?s, _)::_) |- m4 ?s = true] => inversion H;subst;auto
      | [H: SetT ((?s, _)::_) |- mt ?s = true] => inversion H;subst;auto
  | [H: SetU ((?s, _)::_) |- u ?s = true] => inversion H;subst;auto      
    | [H: SetL ((?s, _)::_) |- u ?s = false] => inversion H;subst;auto

 | [H: SetK (?s::_) |- m4 (fst ?s) = false] => inversion H;subst;intuition
    | [H: SetK4 (?s::_) |- m4 (fst ?s) = true] => inversion H;subst;intuition
      | [H: SetT (?s::_) |- mt (fst ?s) = true] => inversion H;subst;intuition
  | [H: SetU (?s::_) |- u (fst ?s) = true] => inversion H;subst;intuition
    | [H: SetL (?s::_) |- u (fst ?s) = false] => inversion H;subst;intuition

     
    | [H: SetU (_::?K) |- SetU ?K] => inversion H;subst;auto
   | [H: SetL (_::?K) |- SetL ?K] => inversion H;subst;auto
   | [H: SetK (_::?K) |- SetK ?K] => inversion H;subst;auto
   | [H: SetK4 (_::?K) |- SetK4 ?K] => inversion H;subst;auto
   | [H: SetT (_::?K) |- SetT ?K] => inversion H;subst;auto 
  end;auto.
 
(*  Ltac solveSignature := solveSignature1; 
 try
  match goal with
  | [H: SetK ((?s, _)::?K) |- m4 ?s = false] => inversion H;subst;auto
    | [H: SetK4 ((?s, _)::?K) |- m4 ?s = true] => inversion H;subst;auto
      | [H: SetT ((?s, _)::?K) |- mt ?s = true] => inversion H;subst;auto
  | [H: SetU ((?s, _)::?K) |- u ?s = true] => inversion H;subst;auto      
    | [H: SetL ((?s, _)::?K) |- u ?s = false] => inversion H;subst;auto
     
  end. *)
 
 
 Ltac simplEmpty := 
 repeat    
  multimatch goal with

  | [H: LtX loc ?K, H1: SetK4 ?K |- _  ] =>  assert(K=[]) by apply (SetK4LocEmpty _ H H1);clear H H1 
 
  | [H: SetU ?K, H1: SetL ?K |- _  ] =>  assert(K=[]) by apply (SetKK4_then_empty _ _ H H1);clear H H1 
  | [H: SetK4 ?K, H1: SetK ?K |- _  ] =>  assert(K=[]) by apply (SetKK4_then_empty _ _ H H1);clear H H1 

  | [H: SetK ?K, H0: LtX ?i ?K, H1:  m4 ?i = true |- _  ] =>  assert(K=[]) by apply (SetKK4_then_empty' _ _ H H0 H1);clear H 

  | [H: SetL ?K, H0: LtX ?i ?K, H1:  u ?i = true |- _  ] =>  assert(K=[]) by apply (SetUL_then_empty' _ _ H H0 H1);clear H 

  | [  |- context[getL(getU _)] ] => rewrite getLgetU 
  | [ H: context[getL(getU _)] |- _  ] => rewrite getLgetU in H
  | [  |- context[getU(getL _)] ] => rewrite getUgetL 
  | [ H: context[getU(getL _)] |- _  ] => rewrite getUgetL in H
  | [  |- context[getL (Loc _)] ] => rewrite getLELoc
  | [ H: context[getL (Loc _)] |- _  ] => rewrite getLELoc in H

  | [ H: SetU ?K |- context[getL ?K] ] => rewrite (SetU_then_empty _ H)
  | [ H1: SetU ?K, H2: context[getL ?K] |- _ ] => rewrite (SetU_then_empty _ H1) in H2

  | [ H: SetL ?K |- context[getU ?K] ] => rewrite (SetL_then_empty _ H)
  | [ H1: SetL ?K, H2: context[getU ?K] |- _ ] => rewrite (SetL_then_empty _ H1) in H2
  
   
 | [ H: SetU (getL ?K)  |- context[getL ?K] ] => rewrite (getLtoSetU _ H)
  | [H0: SetU (getL ?K), H: context[getL ?K] |- _  ] => rewrite (getLtoSetU _ H0) in H

 | [ H: SetU ?K  |- context[getL (PlusT ?K)] ] => rewrite (getLgetUPlusT' _ H)
  | [H0: SetU ?K, H: context[getL (PlusT ?K)] |- _  ] => rewrite (getLgetUPlusT' _ H0) in H

 | [  |- context[getL (PlusT (getU _))] ] => rewrite getLgetUPlusT
  | [H: context[getL (PlusT (getU _))] |- _  ] => rewrite getLgetUPlusT in H
| [  |- context[getU (PlusT (getL _))] ] => rewrite getUgetLPlusT
  | [H: context[getU (PlusT (getL _))] |- _  ] => rewrite getUgetLPlusT in H

 | [H: SetU (getL ?K) |- context[getL ?K]  ] => rewrite (getLtoSetU _ H)
 
  | [H: SetU (getL ?K), H1: context[getL ?K] |- _  ] => rewrite (getLtoSetU _ H) in H1
end.


Ltac simplFix := 
 repeat    
  multimatch goal with
  | [  |- context[PlusT (PlusT _)] ] => rewrite MapPlusT_fixpoint
 | [H:  context[PlusT (PlusT _)]  |- _ ]  => rewrite MapPlusT_fixpoint in H

 | [  |- context[getU (getU _)] ] => rewrite getU_fixpoint
 | [H:  context[getU (getU _)]  |- _ ]  => rewrite getU_fixpoint in H

 | [  |- context[getL (getL _)] ] => rewrite getL_fixpoint
 | [H:  context[getL (getL _)]  |- _ ]  => rewrite getL_fixpoint in H

 | [  |- context[getU (Loc _)] ] => rewrite getULoc
 | [H:  context[getU (Loc _)]  |- _ ]  => rewrite getULoc in H

 | [H: SetT ?K  |- context[PlusT ?K] ] => rewrite (SetTPlusT _ H)
 | [H: SetT ?K, H1: context[PlusT ?K]  |- _ ]  => rewrite (SetTPlusT _ H) in H1

 | [H: SetU ?K  |- context[getU ?K] ] => rewrite (setUtoGetU _ H)
 | [H: SetU ?K, H1: context[getU ?K]  |- _ ]  => rewrite (setUtoGetU _ H) in H1

 | [H: SetL ?K  |- context[getL ?K] ] => rewrite (setLtoGetL _ H)
 | [H: SetL ?K, H1: context[getL ?K]  |- _ ]  => rewrite (setLtoGetL _ H) in H1


| [  |- context[getU (PlusT (getU _))] ] => rewrite getUPlusTgetU'
 | [H: context[getU (PlusT (getU _))]  |- _ ]  => rewrite getUPlusTgetU' in H

| [  |- context[getL (PlusT (getL _))] ] => rewrite getUPlusTgetL'
 | [H: context[getL (PlusT (getL _))]  |- _ ]  => rewrite getUPlusTgetL' in H

| [  |- context[PlusT (getU _)] ] => rewrite  PlusTgetU
 | [H: context[PlusT (getU _)]  |- _ ]  => rewrite  PlusTgetU in H

| [  |- context[PlusT (getL _)] ] => rewrite  PlusTgetL
 | [H: context[PlusT (getL _)]  |- _ ]  => rewrite  PlusTgetL  in H
end.




Ltac simplCtx :=
 multimatch goal with
 
 | [  |- context[PlusT(_++_)] ] => setoid_rewrite PlusTApp
 | [ H: context[PlusT(_++_)] |- _ ] => setoid_rewrite PlusTApp in H 
 | [  |- context[getU(_++_)] ] => setoid_rewrite getUApp
 | [  |- context[getL(_++_)] ] => setoid_rewrite getLApp
 | [ H: context[getU(_++_)] |- _ ] => setoid_rewrite getUApp in H
 | [ H: context[getL(_++_)] |- _ ] => setoid_rewrite getLApp in H
  | [  |- context[(second (getU ?K++getL ?K))] ] => rewrite <- cxtDestructSecond
 | [ H:context[(second (getU ?K++getL ?K))] |- _ ] => rewrite <- cxtDestructSecond in H 
end. 

 
Ltac solveSignature2 :=
 match goal with
  | [ H: SetX ?s ?b ?K |- SetX ?s ?b (getU ?K)] => apply SetK4Destruct in H;sauto
  | [ H: SetX ?s ?b ?K |- SetX ?s ?b (getL ?K)] => apply SetK4Destruct in H;sauto

| [ H: SetX ?s ?b ?K, H2: Permutation (getU ?K) (?K2 ++ _) |- SetX ?s ?b ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 | [ H: SetX ?s ?b ?K, H2: Permutation (getU ?K) (_ ++ ?K2) |- SetX ?s ?b ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2

  | [H: Permutation (getU ?CN) (_ ++ ?M) |- SetU ?N] =>  apply getUPerm_SetU in H;solveSignature2
  | [H: Permutation (getU ?CN) (?M ++ _) |- SetU ?M] =>  apply getUPerm_SetU in H;solveSignature2

 | [ H: SetT ?K |- SetT (getU ?K)] => rewrite cxtDestruct in H;solveSignature2
 | [ H: SetT ?K |- SetT (getL ?K)] => rewrite cxtDestruct in H;solveSignature2
 
 | [ H1: u ?i = false, H2: In (?i, ?F) ?B  |- In (?i, ?F) (getL ?B) ] => apply lIngetL;auto

end.
 