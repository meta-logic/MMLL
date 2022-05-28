Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.LK.LKBipoles.
Import MMLL.Misc.Permutations.
Require Import MMLL.SL.FLLReasoning.
Require Import MMLL.SL.InvPositivePhase.
         
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section LKCutL.

Context {SI: Signature}.

 Definition CutC (h: nat) (a:subexp):= forall m n n' i j FC M N L,
    m <= h ->
    m = i + j ->
    n' <= n ->
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL N ->
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second L) ->
    mt a = true ->
    (seqN (LK a) i ((a,u|FC|)::L) M (UP []) ->
     seqN (LK a) j ((a,d|FC|)::L) N (UP []) -> 
     seq (LKC a (pred n)) L (M ++ N) (UP [])).
 
  Definition CutL (h: nat) (a:subexp) := forall m n n' i j FC M N L,
    m <= h ->
    m = i + j ->
    n' <= n ->
    isOLFormula FC ->
    lengthUexp FC n' ->
    IsPositiveAtomFormulaL N ->
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second L) ->
    mt a = true ->
    (seqN (LK a) i L (u| FC | :: M) (UP []) ->
     seqN (LK a) j L (d| FC | :: N) (UP []) ->
     seq (LKC a (pred n)) L (M ++ N) (UP [])).

Ltac CutTacPOSNEG := sauto;
  try
    match goal with
    | [ |- isFormula _] => constructor;auto
    | [ |- IsPositiveAtomFormula _] =>  constructor;auto
    | [ |- LKC _ _] => autounfold; solve[constructor;constructor;auto]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
      solve [apply PositiveAtomIn in H';auto;contradiction]
    | [ H: seqN _ _ _ _ (DW zero) |- _] => invTri H
    | [ H: seq  _ _ _ (DW zero) |- _] => invTri' H
    | [ |- LKC _ _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [ |- LK _ ]=> autounfold;solve [repeat (constructor;auto)]
    | [|- IsPositiveAtomFormulaL (d| _ | :: _)] => solve[repeat (constructor;auto)]
    end; OLSolve.

 Ltac solveBipole :=
 match goal with
| [H: context[CteBipole] |- _] => inversion H 
| [H: context[BinBipole] |- _] => inversion H
| [H: context[QuBipole] |- _] => inversion H  end.

Tactic Notation "Bipole"  constr(B) constr(S):=
        match B with 
        | TT => TFocus (CteBipole TT_BODY S)
        | FF => TFocus (CteBipole FF_BODY S)
end.

(* ; [do 2 constructor;OLSolve | solveBipole | ].
 *)
Tactic Notation "Bipole"  constr(B) constr(S) constr(F) constr(G):= 
     match B with
     | AND => TFocus (BinBipole AND_BODY S F G)
     | OR => TFocus (BinBipole OR_BODY S F G)
     | IMP => TFocus (BinBipole IMP_BODY S F G) 
  end.
  
  
Tactic Notation "Bipole"  constr(B) constr(S) constr(FX) :=
    match B with
     | ALL => TFocus (QuBipole ALL_BODY S FX)
     | SOME => TFocus (QuBipole SOME_BODY S FX)
  end.
  
  Ltac LLSwapL H :=
        let Hs := type of H in 
        match Hs with
        |  (seqN _ _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLCN with (LC':= (G :: F :: L)) in H;[|perm]
        |  (seq  _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLC with (LC':= (G :: F :: L)) in H;[|perm]
        end.

Lemma exchangeSwap n th L F A B C: Permutation A (B ::C)
 -> seqN th n L (F :: A) (UP []) -> seqN th n L (B :: F :: C) (UP []).
 Proof with sauto.
 intros.
 eapply exchangeLCN.
 2: exact H0.
 rewrite H...
 Qed.
        
Ltac PermSwap Hs Hp:=
    eapply exchangeSwap in Hs;[| exact Hp].

Lemma exchangeSwap2 n th L F G A B C: Permutation A (B ::C)
 -> seqN th n L (F :: G :: A) (UP []) -> seqN th n L (B :: F :: G :: C) (UP []).
 Proof with sauto.
 intros.
 eapply exchangeLCN.
 2: exact H0.
 rewrite H...
 Qed.
        
Ltac PermSwap2 Hs Hp:=
    eapply exchangeSwap2 in Hs;[| exact Hp].


Ltac applyCutL Hl Hr :=
 match goal with
  [ C: CutL _ _, 
    Hc: lengthUexp ?P ?n |- seq _ _ (?M++?N) _  ] =>
    match type of Hl with
      | seqN _ ?l _ (u| ?P|::?M) _  =>
         match type of Hr with
         | seqN _ ?r _ (d| ?P|::?N) _ =>
           let H' := fresh "H" in 
           assert(H' : l + r = l + r) by auto;
           refine(C _ _ _ _ _ _ _ _ _ _  H'  _ _ Hc _ _ _ _ Hl Hr);
           CutTacPOSNEG
          | _ => idtac
          end
     | _ => idtac      
   end
end.
   
Ltac applyCutC Hl Hr :=
 match goal with
  [ C: CutC _ _, 
    Hc: lengthUexp ?P ?n |- seq _ ?L (?M++?N) _  ] =>
    match type of Hl with
      | seqN _ ?l ((?i, u| ?P|)::?L) ?M _  =>
         match type of Hr with
         | seqN _ ?r ((?i, d| ?P|)::?L) ?N _ =>
           let H' := fresh "H" in assert(H' : l + r = l + r) by auto;
           refine(C _ _ _ _ _ _ _ _ _ _  H'  _ _ Hc _ _ _ _ Hl Hr);
           CutTacPOSNEG
          | _ => idtac
          end
     | _ => idtac      
   end
end.   

 
Ltac BinCut :=
  match goal with
  |  [ Hp: Permutation ?N ((atom (?a ?P))::?y), 
     H2 : seqN _ ?n _ ((atom (?a ?F)) :: ?N) (UP []),
     H1 : seqN _ ?m _ ((atom (?b ?P)) :: ?M) (UP []) |- 
     seq _ _ (?M ++ (atom (?a ?F)) :: ?y) _ ] => 
        PermSwap H2 Hp;
        applyCutL H1 H2
   
   |  [ Hp: Permutation ?x ((atom (?b ?P))::?y), 
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?a ?P)) :: _) (UP []) |- 
       seq _ _ (_ ++ (atom (?a ?F)) :: ?y) _ ] => 
       PermSwap Hs Hp;
       applyCutL Hh Hs

  |  [ Hp: Permutation ?x ((atom (?a ?P))::?y), 
     Hs : seqN _ ?n _ ((atom (?a ?F)) :: ?x) (UP []),
     Hh : seqN _ ?m _ ((atom (?b ?P)) :: _) (UP []) |- 
     seq _ _ (_ ++ (atom (?a ?F)) :: ?y) _ ] => 
        PermSwap Hs Hp;
        applyCutL Hh Hs
   
   |  [ Hp: Permutation ?x ((atom (?b ?P))::?y), 
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?a ?P)) :: _) (UP []) |- 
       seq _ _ (_ ++ (atom (?a ?F)) :: ?y) _ ] => 
       PermSwap Hs Hp;
       applyCutL Hh Hs
                      
    |  [
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: (atom (?a ?P)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?b ?P)) :: _) (UP []) |- 
       seq _ _ (_ ++ (atom (?a ?F)) :: ?x) _ ] => 
       LLSwapL Hs;
       applyCutL Hh Hs
     |  [
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: (atom (?b ?P)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?a ?P)) :: _) (UP []) |- 
       seq _ _ (_ ++ (atom (?a ?F)) :: ?x) _ ] => LLSwapL Hs;
       applyCutL Hh Hs
       end.

Ltac permuteANDR :=              
  match goal with 
  | [ H1 : seqN _ _ _ _ (DW (AND_BODY.(rb_rightBody) _ _)),
       H2 : Permutation ?N (u| t_bin AND ?F ?G | :: ?x) |- 
       seq _ _ (?M ++ ?N) (UP []) ] => 
       
      apply FocusingWith in H1;sauto;
      TFocus (BinBipole AND_BODY Right F G); 
      simpl;
      LLTensor [u| t_bin AND F G | ] (M++x);[
      rewrite H2;sauto  |  
      solveLL;LLStore ; rewrite <- Permutation_midle ]
 
  | [ H1 : seqN _ _ _ _ (DW (AND_BODY.(rb_rightBody) _ _)),
       H2 : Permutation ?M (u| t_bin AND ?F ?G | :: ?x) |- 
       seq _ _ (?M ++ ?N) (UP []) ] => 
       
      apply FocusingWith in H1;sauto;
      TFocus (BinBipole AND_BODY Right F G); 
      simpl;
      LLTensor [u| t_bin AND F G | ] (x++N);[
      rewrite H2;sauto  |  
      solveLL;LLStore  ]   
  end.
  
   




Ltac permuteANDRight :=              
    match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin AND ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole AND_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin AND F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin AND ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole AND_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
            end;try BinCut. 



Ltac permuteANDLeft :=              
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ?N (d| t_bin AND ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin AND F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusL;solveLL;rewrite <- Permutation_midle ]
        | 
         TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin AND F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusR;solveLL;rewrite <- Permutation_midle ]] 
        
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ((?i, d| t_bin AND ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusL;solveLL; rewrite <- Permutation_midle ]
        |
        TFocus (BinBipole AND_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusR;solveLL; rewrite <- Permutation_midle ]
        ]     
     end;try BinCut. 
        
   Ltac permuteORRight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin OR ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin OR F G | ] (M++x);
        [rewrite Hpp;sauto  |  LLPlusL;solveLL;rewrite <- Permutation_midle ]
        | TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin OR F G | ] (M++x);
        [rewrite Hpp;sauto  | LLPlusR;solveLL;rewrite <- Permutation_midle ]
        ]  
   | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin OR ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPlus in H;sauto;[
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusL;solveLL; rewrite <- Permutation_midle ]
        |
        TFocus (BinBipole OR_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  LLPlusR;solveLL; rewrite <- Permutation_midle ]
        ]     
     end;try BinCut. 
 
  
 Ltac permuteORLeft :=              
              
                match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ?N (d| t_bin OR ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole OR_BODY Left F G); 
        simpl;
        LLTensor [d| t_bin OR F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
         | [ H : seqN _ _ _ _ (DW (rb_leftBody _ _)) ,
        Hpp: Permutation ((?i, d| t_bin OR ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingWith in H;sauto;
        TFocus (BinBipole OR_BODY Left F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL  |  solveLL;LLStore ; rewrite <- Permutation_midle ]
      
            end;try BinCut.
   
   
            
               
 Ltac permuteIMPRight :=              
 match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ?N (u| t_bin IMP ?F ?G | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor [u| t_bin IMP F G | ] (M++x);[
        rewrite Hpp;sauto  |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end;
            
        match goal with
      [C: CutL _ _, Hp: Permutation ?x (d| ?P |::?y), 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN _ ?n _ (u| ?G | :: d| ?F | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => PermSwap2 Hs Hp;assert(Heq : m + n = m + n) by auto;
       refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh Hs);CutTacPOSNEG;OLSolve 
       
       end.

  Theorem FocusingForallUP :
    forall n th (y: expr con) FX D G, proper y ->
    seqN th n G D (DW (∀{ fun x : expr con => u| FX x |})) ->
      exists m , n =  S (S (S m))  /\ seqN th m G (u| FX y |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    solveF.
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split;eauto.
  Qed.
         
   Theorem FocusingForallDW :
    forall n th (y: expr Syntax.con) FX D G, proper y ->
    seqN th n G D (DW (∀{ fun x : expr Syntax.con => d| FX x |})) ->
      exists m , n =  S (S (S m))  /\ seqN th m G (d| FX y |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    solveF.
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split;eauto.
  Qed.

   Theorem FocusingExistsUP :
    forall n th FX D G, 
    seqN th n G D (DW (∃{ fun x : expr Syntax.con => u| FX x |})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ seqN th m G (u| FX t |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... solveF. 
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.

   Theorem FocusingExistsDW :
    forall n th FX D G, 
    seqN th n G D (DW (∃{ fun x : expr Syntax.con => d| FX x |})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ seqN th m G (d| FX t |::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... solveF. 
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.

Ltac CutQu :=      
     match goal with
      [C: CutL _ _, Hp: Permutation ?x ((atom (?b ?P))::?y), 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?a ?P)) :: _) (UP []) |- 
       seq _ _ ((atom (?a ?F)) :: _++ ?y) _ ] => 
       rewrite <- Permutation_midle;
 
 PermSwap Hs Hp;assert(Heq : m + n = m + n) by auto;
       refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh Hs);CutTacPOSNEG;OLSolve 
 
   |   [C: CutL _ _, Hp: Permutation ?x ((atom (?a ?P))::?y), 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN _ ?n _ ((atom (?a ?F)) :: ?x) (UP []),
       Hh : seqN _ ?m _ ((atom (?b ?P)) :: _) (UP []) |- 
       seq _ _ ((atom (?a ?F)) :: _++ ?y) _ ] => 
       rewrite <- Permutation_midle;
 
 PermSwap Hs Hp;assert(Heq : m + n = m + n) by auto;
       refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh Hs);CutTacPOSNEG;OLSolve 
   
       |  [ C: CutL _ _,
       HF:  lengthUexp (?P) ?o,
       Hs : seqN _ ?n _ ( atom (?a ?F) :: atom (?b ?P) :: ?x) (UP []),
       Hh : seqN _ ?m _ (atom (?a ?P) :: _) (UP []) |- 
       seq _ _ (atom (?a ?F ) :: _ ++ ?x) _ ] => 
       rewrite <- Permutation_midle;
       LLSwapL Hs;
       assert(Heq : m + n = m + n) by auto;
       refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh Hs);CutTacPOSNEG;OLSolve 
     
       |  [ C: CutL _ _,
       HF:  lengthUexp (?P) ?o,
       Hs : seqN _ ?n _ ( atom (?a ?F) :: atom (?a ?P) :: ?x) (UP []),
       Hh : seqN _ ?m _ (atom (?b ?P) :: _) (UP []) |- 
       seq _ _ (atom (?a ?F ) :: _ ++ ?x) _ ] => 
       rewrite <- Permutation_midle;
       LLSwapL Hs;
       assert(Heq : m + n = m + n) by auto;
       refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh Hs);CutTacPOSNEG;OLSolve 
       end.
               
 Ltac permuteALLRight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ?N (u| t_quant ALL ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole ALL_BODY Right FX);
      simpl;
      LLTensor [u| t_quant ALL FX | ] (M++x);
       [  rewrite Hpp;sauto |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallUP _ Hpro H) as Hj';sauto
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ((?i, u| t_quant ALL ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole ALL_BODY Right FX);
      simpl;
      LLTensor (@nil oo) (M++N);
       [  solveLL |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallUP _ Hpro H) as Hj';sauto
       end
      end; try CutQu.
    
 Ltac permuteALLLeft :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ?N (d| t_quant ALL ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsDW in H;sauto; 
        TFocus (QuBipole ALL_BODY Left FX); 
        simpl;
        LLTensor [d| t_quant ALL FX | ] (M++x);[
        rewrite Hpp;sauto |  ] ; match goal with
      [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ((?i, d| t_quant ALL ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsDW in H;sauto; 
        TFocus (QuBipole ALL_BODY Left FX); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  ]; match goal with
       [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
  end; try CutQu.

 Ltac permuteSOMERight :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ?N (u| t_quant SOME ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsUP in H;sauto; 
        TFocus (QuBipole SOME_BODY Right FX); 
        simpl;
        LLTensor [u| t_quant SOME FX | ] (M++x);[
        rewrite Hpp;sauto |  ] ; match goal with
      [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_rightBody _)) ,
        Hpp: Permutation ((?i, u| t_quant SOME ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
     apply FocusingExistsUP in H;sauto; 
        TFocus (QuBipole SOME_BODY Right FX); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  ]; match goal with
       [Hpro: proper ?x |- _] => 
            LLExists x; LLRelease; LLStore
       end
  end; try CutQu.
        
   Ltac permuteSOMELeft :=              
   match goal with 
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ?N (d| t_quant SOME ?FX | :: ?x)
         |- 
        seq _ _ (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole SOME_BODY Left FX);
      simpl;
      LLTensor [d| t_quant SOME FX | ] (M++x);
       [  rewrite Hpp;sauto |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallDW _ Hpro H) as Hj';sauto
       end
       
    | [ H : seqN _ _ _ _ (DW (rq_leftBody _)) ,
        Hpp: Permutation ((?i, d| t_quant SOME ?FX |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
      
      TFocus (QuBipole SOME_BODY Left FX);
      simpl;
      LLTensor (@nil oo) (M++N);
       [  solveLL |  
       LLRelease; LLForall; try solveUniform;LLStore 
       ]; match goal with
       [Hpro: proper ?x |- context[?x]] =>          specialize(FocusingForallDW _ Hpro H) as Hj';sauto
       end
      end; CutQu.
      
  Context  {USI:UnbSignature}.
  Context  {UND:UnbNoDSignature}.
  
Ltac FocusClause C L A B:=
     match C with
     | AND => match L with
                      | up => TFocus (BinBipole AND_BODY Right A B)
                      | down => TFocus (BinBipole AND_BODY Left A B)
                      end
     | OR => match L with
                      | up => TFocus (BinBipole OR_BODY Right A B)
                      | down => TFocus (BinBipole OR_BODY Left A B)
                      end
     | IMP => match L with
                      | up => TFocus (BinBipole IMP_BODY Right A B)
                      | down => TFocus (BinBipole IMP_BODY Left A B)
                      end
    end.
    
Ltac permute := 
match goal with
 | [ H : Permutation ?M (atom (?a (t_bin ?C ?A ?B)) :: ?x) |- 
       seq _ _ (?M ++ ?N) _] => FocusClause C a A B
 | [ H : Permutation ?N (atom (?a (t_bin ?C ?A ?B)) :: ?x) |- 
       seq _ _ (?M ++ ?N) _] => FocusClause C a A B
 end.
 
 Ltac solveQF :=
  match goal with
   [ H1 : isOLFormula (t_quant qt ?FX), 
     H2 : proper ?x |- isOLFormula (?FX ?x)] =>
                inversion H1;subst;OLSolve;
                match goal with
       [ H : lbind 0%nat _ = lbind 0%nat ?FX |-
          isOLFormula (?FX ?x)] =>
                apply lbindEq in H;sauto;
               try rewrite <- H;sauto
              end  
                
   end.  
  
  Lemma LKCutL F F0 FC L M N a h n0 n1 n' n:
     mt a = true -> S h = S n0 + S n1 -> isOLFormula FC ->
     lengthUexp FC n' -> 
     n' <= n ->
     IsPositiveAtomFormulaL M ->
     IsPositiveAtomFormulaL N ->
     IsPositiveAtomFormulaL (second L) ->
     CutL h a ->
     CutC h a ->
     seqN (LK a) (S n0) L (u| FC | :: M) (UP []) ->
     seqN (LK a) (S n1) L (d| FC | :: N) (UP []) ->
     LK a F ->
     ~ IsPositiveAtom F ->
     seqN (LK a) n0 L (u| FC | :: M) (DW F) ->
     LK a F0 ->
     ~ IsPositiveAtom F0 ->
     seqN (LK a) n1 L (d| FC | :: N) (DW F0) ->
     seq (LKC a (pred n)) L (M ++ N) (UP []).
Proof with CutTacPOSNEG.     
    intros H4 Heqh isFFC lngF HRel isFM isFN isFL. 
    intros CutHL CutHC.
    intros Hi Hj.
    intros H H0 H1 H2 H3 H5.

   inversion H;sauto. 
   (* Analizing the derivation on the left *)     
   * (* 1/6 - Constants *)
      inversion H6;sauto.
      (* Four Cases *)     
      ** (* 1/4 - TT Right *)
      apply BipoleReasoning in H1...
      inversion H10...
      solveF.
      inversion H10...
      solveF.
      ** (* 2/4 - TT Left *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      Bipole TT Left.
      LLTensor [d| t_cons TT | ] (N++x1).
      rewrite H9...
      simpl. solveLL.
      simpl in H12.
      Bipole TT Left.
      LLTensor (@nil oo) (M++N). 
      solveLL.
      simpl. solveLL.
      ** (* 3/4 - FF Right *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      {  inversion H8...
          (** FF Right is principal *)
          LLrewrite H9 in H10. 
          clear H9.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H11...
                solveF.
                inversion H11...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H12.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H9...
                simpl...
                simpl in H13.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H7.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H5...
                simpl...
                simpl in H9.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H11... 
                solveF.
                inversion H11... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDRight.
                simpl in H14.
                permuteANDRight.
              -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDLeft.
                simpl in H14.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORRight.  
                simpl in H14.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORLeft.
                simpl in H14.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteIMPRight.  
                simpl in H14.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                apply FocusingTensor in H12...
                rewrite H14 in H9.
                checkPermutationCases H9.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H11...
                LLTensor (M++x0) x5. 
                rewrite <- H12...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H11...
                LLTensor x4 (M++x0). 
                rewrite <- H12...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H12...
                checkPermutationCases H13.
                TFocus (BinBipole IMP_BODY Left F G). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H12 H9.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H12)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H12.
      refine (WeakTheory _ _ H12)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H8.
             
             inversion H8...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H8...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H11. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteALLRight.
                solveQF.
                simpl in H15. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteALLLeft.
               solveQF.
               simpl in H15.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMERight.
               solveQF.
               simpl in H15.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMELeft.
               solveQF.
               simpl in H15.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
            inversion H5...
            apply FocusingQuest in H11...
            rewrite H9.
            apply AbsorptionL with (i:=a) in Hi...
           assert(Heq : S (S x) + x2 = S (S x) + x2) by auto. 
      refine(CutHC _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H7)...
             apply FocusingQuest in H11...
             rewrite H5 in H12.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. 
            
            apply FocusingQuest in H11...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
             
             inversion H11...
             inversion H16...
             2:solveF.     
             rewrite H5 in H17.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. 
            
            inversion H11...
             inversion H16...
             2:solveF.     
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. }
   
    (* Continuing the case 3/4 - FF Right *) 
    Bipole FF Right. 
    LLTensor [u| t_cons FF |] (x1++N).
    rewrite H9...
    simpl...
    
    Bipole FF Right. 
    LLTensor (@nil oo) (M++N).
    solveLL.
    simpl...
      
      ** (* 4/4 - FF Left *)
      apply BipoleReasoning in H1...
      inversion H10...
      solveF.
      inversion H10...
      solveF.
 
     * (* 2/6 - Connectives *)
        inversion H6;sauto. 
      ** (* 1/6 - AND RIGHT *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      { inversion H8...
         (** AND Right is principal *)
          LLrewrite H9 in H10. 
          clear H9.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H12...
                solveF.
                inversion H12...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H12... 
                solveF.
                inversion H12... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDRight.
                simpl in H14.
                permuteANDRight.
              -- apply BipoleReasoning in H5...
                  checkPermutationCases H13.
                 { (** CUT-COHERENT CASE *) 
                     inversion H9...
                     rewrite H11.
                     inversion lngF...
                     Import MMLL.SL.CutElimination.
                    eapply GeneralCut' with (C:=dual (AND_BODY.(rb_leftBody) F G0)).      
                    2:{ apply seqNtoSeq in H12.  
                          refine (WeakTheory _ _ H12)...
                          apply TheoryEmb1. }
         
                     rewrite <- (app_nil_l M).
                     eapply GeneralCut' with (C:=dual (AND_BODY.(rb_rightBody) F G0)).  
                    2:{ apply seqNtoSeq in H10.
                           refine (WeakTheory _ _ H10)...
                           apply TheoryEmb1. }
                     
                    eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
                     intros.
                     apply TheoryEmb2.
                     refine(CuteRuleN H5 _)...
                     apply weakeningAll...      
                     apply AND_CUTCOHERENT... }
    
    (*   apply FocusingWith in H10...
          apply FocusingPlus in H12...
          rewrite H11.
          inversion lngF...
          assert(Heq : x2 + x = x2 + x) by auto. 
                 
          refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ H15 _ _ _ _ H10 H9)...
          rewrite H11.
          inversion lngF...
          assert(Heq : x2 + x = x2 + x) by auto. 
                 
           refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ H16 _ _ _ _ H13 H9)...  *)
  
                permuteANDLeft.
                simpl in H14.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORRight.  
                simpl in H14.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORLeft.
                simpl in H14.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteIMPRight.  
                simpl in H14.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                apply FocusingTensor in H12...
                rewrite H14 in H9.
                checkPermutationCases H9.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor (M++x0) x5. 
                rewrite <- H12...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor x4 (M++x0). 
                rewrite <- H12...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H12...
                checkPermutationCases H13.
                TFocus (BinBipole IMP_BODY Left F G0). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H12 H9.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H12)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H12.
      refine (WeakTheory _ _ H12)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H8.
             
             inversion H8...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H8...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H11. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteALLRight.
                solveQF.
                simpl in H15. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteALLLeft.
               solveQF.
               simpl in H15.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMERight.
               solveQF.
               simpl in H15.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMELeft.
               solveQF.
               simpl in H15.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
            inversion H5...
            apply FocusingQuest in H11...
            rewrite H9.
            apply AbsorptionL with (i:=a) in Hi...
           assert(Heq : S (S x) + x2 = S (S x) + x2) by auto. 
      refine(CutHC _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
             apply FocusingQuest in H11...
             rewrite H5 in H12.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. 
            
            apply FocusingQuest in H11...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
             
             inversion H11...
             inversion H16...
             2:solveF.     
             rewrite H5 in H17.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. 
            
            inversion H11...
             inversion H16...
             2:solveF.     
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. }
     
      apply FocusingWith in H10...
      TFocus (BinBipole AND_BODY Right F1 G). 
      simpl.
      LLTensor [u| t_bin AND F1 G | ] (N++x1).
      rewrite H9...
      LLRelease.
      LLWith. 1-2: LLStore.
      PermSwap H12 H8.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H12 Hj)...
      LLExact H1.
      PermSwap H13 H8.
      assert(seq (LKC a (pred n)) L ((u| G | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H13 Hj)...
      LLExact H1.
      
      simpl in H10.
      apply FocusingWith in H10...
      TFocus (BinBipole AND_BODY Right F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      
      LLRelease.
      LLWith. 1-2: LLStore.
      LLSwapL H11.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      LLSwapL H13.
      assert(seq (LKC a (pred n)) L ((u| G | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H13 Hj)...
      LLExact H1.
      ** (* 2/6 - AND LEFT *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      apply FocusingPlus in H10...
      TFocus (BinBipole AND_BODY Left F1 G). 
      simpl.
      LLTensor [d| t_bin AND F1 G | ] (N++x1).
      rewrite H9...
      LLPlusL.
      LLRelease. LLStore.
      PermSwap H11 H8.
      assert(seq (LKC a (pred n)) L ((d| F1 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      TFocus (BinBipole AND_BODY Left F1 G). 
      simpl.
      LLTensor [d| t_bin AND F1 G | ] (N++x1).
      rewrite H9...
      LLPlusR.
      LLRelease. LLStore.
      PermSwap H11 H8.
      assert(seq (LKC a (pred n)) L ((d| G | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      simpl in H10.
      apply FocusingPlus in H10...
      
      TFocus (BinBipole AND_BODY Left F1 G).
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLPlusL.
      LLRelease. LLStore.
     
      LLSwapL H10.
      assert(seq (LKC a (pred n)) L ((d| F1 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
      LLExact H1.
      
      TFocus (BinBipole AND_BODY Left F1 G).
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLPlusR.
      LLRelease. LLStore.
     
      LLSwapL H10.
      assert(seq (LKC a (pred n)) L ((d| G | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
      LLExact H1.
      ** (* 3/6 - OR LEFT *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      { inversion H8...
         (** OR Left is principal *)
          LLrewrite H9 in H10. 
          clear H9.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H12...
                solveF.
                inversion H12...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H12... 
                solveF.
                inversion H12... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDRight.
                simpl in H14.
                permuteANDRight.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDLeft.
                simpl in H14.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORRight.  
                simpl in H14.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                 { (** CUT-COHERENT CASE *) 
                     inversion H9...
                     rewrite H11.
                     inversion lngF...
                    eapply GeneralCut' with (C:=dual (OR_BODY.(rb_leftBody) F G0)).      
                    2:{ apply seqNtoSeq in H12.  
                          refine (WeakTheory _ _ H12)...
                          apply TheoryEmb1. }
         
                     rewrite <- (app_nil_l M).
                     eapply GeneralCut' with (C:=dual (OR_BODY.(rb_rightBody) F G0)).  
                    2:{ apply seqNtoSeq in H10.
                           refine (WeakTheory _ _ H10)...
                           apply TheoryEmb1. }
                     
                    eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
                     intros.
                     apply TheoryEmb2.
                     refine(CuteRuleN H5 _)...
                     apply weakeningAll...      
                     apply OR_CUTCOHERENT... }
    
                permuteORLeft.
                simpl in H14.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteIMPRight.  
                simpl in H14.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                apply FocusingTensor in H12...
                rewrite H14 in H9.
                checkPermutationCases H9.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor (M++x0) x5. 
                rewrite <- H12...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor x4 (M++x0). 
                rewrite <- H12...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H12...
                checkPermutationCases H13.
                TFocus (BinBipole IMP_BODY Left F G0). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H12 H9.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H12)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H12.
      refine (WeakTheory _ _ H12)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H8.
             
             inversion H8...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H8...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H11. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteALLRight.
                solveQF.
                simpl in H15. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteALLLeft.
               solveQF.
               simpl in H15.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMERight.
               solveQF.
               simpl in H15.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMELeft.
               solveQF.
               simpl in H15.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
            inversion H5...
            apply FocusingQuest in H11...
            rewrite H9.
            apply AbsorptionL with (i:=a) in Hi...
           assert(Heq : S (S x) + x2 = S (S x) + x2) by auto. 
      refine(CutHC _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
             apply FocusingQuest in H11...
             rewrite H5 in H12.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. 
            
            apply FocusingQuest in H11...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
             
             inversion H11...
             inversion H16...
             2:solveF.     
             rewrite H5 in H17.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. 
            
            inversion H11...
             inversion H16...
             2:solveF.     
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. }
     
      apply FocusingPlus in H10...
      TFocus (BinBipole OR_BODY Right F1 G). 
      simpl.
      LLTensor [u| t_bin OR F1 G | ] (N++x1).
      rewrite H9...
      LLPlusL.
      LLRelease. LLStore.
      
      PermSwap H11 H8.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      TFocus (BinBipole OR_BODY Right F1 G). 
      simpl.
      LLTensor [u| t_bin OR F1 G | ] (N++x1).
      rewrite H9...
      LLPlusR.
      LLRelease. LLStore.
      PermSwap H11 H8.
      assert(seq (LKC a (pred n)) L ((u| G | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      simpl in H10.
      apply FocusingPlus in H10...
      
      TFocus (BinBipole OR_BODY Right F1 G).
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLPlusL.
      LLRelease. LLStore.
     
      LLSwapL H10.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
      LLExact H1.
      
      TFocus (BinBipole OR_BODY Right F1 G).
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLPlusR.
      LLRelease. LLStore.
     
      LLSwapL H10.
      assert(seq (LKC a (pred n)) L ((u| G | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
      LLExact H1.

      ** (* 4/6 - OR Left *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      apply FocusingWith in H10...
      TFocus (BinBipole OR_BODY Left F1 G). 
      simpl.
      LLTensor [d| t_bin OR F1 G | ] (N++x1).
      rewrite H9...
      LLRelease. 
      LLWith. 1-2: LLStore.
      
      PermSwap H12 H8.
      assert(seq (LKC a (pred n)) L ((d| F1 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H12 Hj)...
      LLExact H1.
      
      PermSwap H13 H8.
      assert(seq (LKC a (pred n)) L ((d| G | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H13 Hj)...
      LLExact H1.
      
      simpl in H10.
      apply FocusingWith in H10...
      
      TFocus (BinBipole OR_BODY Left F1 G).
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      
      LLRelease. 
      LLWith. 1-2: LLStore.
      
      LLSwapL H11.
      assert(seq (LKC a (pred n)) L ((d| F1 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      LLSwapL H13.
      assert(seq (LKC a (pred n)) L ((d| G | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H13 Hj)...
      LLExact H1.
      ** (* 5/6 - IMP Right *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      { inversion H8...
         (** IMP Right is principal *)
          LLrewrite H9 in H10. 
          clear H9.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H12...
                solveF.
                inversion H12...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H11...
                simpl...
                simpl in H14.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H12... 
                solveF.
                inversion H12... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteANDRight.
                simpl in H14.
                permuteANDRight.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H13.
                permuteANDLeft.
                simpl in H14.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORRight.  
                simpl in H14.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteORLeft.
                simpl in H14.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteIMPRight.  
                simpl in H14.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H13.
                 { (** CUT-COHERENT CASE *) 
                     inversion H9...
                     rewrite H11.
                     inversion lngF...
                    eapply GeneralCut' with (C:=dual (IMP_BODY.(rb_leftBody) F G0)).      
                    2:{ apply seqNtoSeq in H12.  
                          refine (WeakTheory _ _ H12)...
                          apply TheoryEmb1. }
         
                     rewrite <- (app_nil_l M).
                     eapply GeneralCut' with (C:=dual (IMP_BODY.(rb_rightBody) F G0)).  
                    2:{ apply seqNtoSeq in H10.
                           refine (WeakTheory _ _ H10)...
                           apply TheoryEmb1. }
                     
                    eapply WeakTheory with (th:=(CUTLN (max n1 n2))).
                     intros.
                     apply TheoryEmb2.
                     refine(CuteRuleN H5 _)...
                     apply weakeningAll...      
                     apply IMP_CUTCOHERENT... }
                
                apply FocusingTensor in H12...
                rewrite H14 in H9.
                checkPermutationCases H9.
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor (M++x0) x5. 
                rewrite <- H12...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor [d| t_bin IMP F G0 | ] (M++x2).
                rewrite H11...
                LLTensor x4 (M++x0). 
                rewrite <- H12...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H12...
                checkPermutationCases H13.
                TFocus (BinBipole IMP_BODY Left F G0). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H12 H9.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H12)...
                LLRelease. LLStore.
                apply seqNtoSeq in H16.
      refine (WeakTheory _ _ H16)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G0). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H12.
      refine (WeakTheory _ _ H12)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H16 H9.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H16)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H8.
             
             inversion H8...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H8...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H11. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteALLRight.
                solveQF.
                simpl in H15. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteALLLeft.
               solveQF.
               simpl in H15.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMERight.
               solveQF.
               simpl in H15.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
               permuteSOMELeft.
               solveQF.
               simpl in H15.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
            inversion H5...
            apply FocusingQuest in H11...
            rewrite H9.
            apply AbsorptionL with (i:=a) in Hi...
           assert(Heq : S (S x) + x2 = S (S x) + x2) by auto. 
      refine(CutHC _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H7)...
             apply FocusingQuest in H11...
             rewrite H5 in H12.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. 
            
            apply FocusingQuest in H11...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H11)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H12.
             
             inversion H11...
             inversion H16...
             2:solveF.     
             rewrite H5 in H17.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H9...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. 
            
            inversion H11...
             inversion H16...
             2:solveF.     
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + n1 = S (S x) + n1) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H17)...
            apply allU. }      
      
     
      apply FocusingPar in H10...
      TFocus (BinBipole IMP_BODY Right F1 G). 
      simpl.
      LLTensor [u| t_bin IMP F1 G | ] (N++x1).
      rewrite H9...
      LLRelease. 
      LLPar. do 2 LLStore.
     
      rewrite H8 in H11.
      assert( seqN (LK a) x2 L (u| FC | :: u| G | :: d| F1 | ::  x1) (UP [])).
      LLExact H11.
      assert(seq (LKC a (pred n)) L ((u| G | :: d| F1 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H1 Hj)...
      OLSolve.
      
      LLExact H10.
      
      apply FocusingPar in H10...
      TFocus (BinBipole IMP_BODY Right F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      
      LLRelease. 
      LLPar. do 2 LLStore.
     
       assert( seqN (LK a) x2 L (u| FC | :: u| G | :: d| F1 | ::  M) (UP [])).
      LLExact H10.
      assert(seq (LKC a (pred n)) L ((u| G | :: d| F1 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H1 Hj)...
      
      LLExact H8.
      ** (* 6/6 - IMP LEFT *)
      apply BipoleReasoning in H1...
      checkPermutationCases H11.
      assert(isFx1: IsPositiveAtomFormulaL x1).
      OLSolve.
      apply FocusingTensor in H10...
      rewrite H12 in H8.
      checkPermutationCases H8.
      
      TFocus (BinBipole IMP_BODY Left F1 G). 
      simpl.
      LLTensor [d| t_bin IMP F1 G | ] (N++x1).
      rewrite H9...
      LLTensor (x++N) x4.
      rewrite <- H10... 
      LLRelease. LLStore.
      PermSwap H11 H8.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: x) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H11 Hj)...
      LLExact H1.
      
      LLRelease.
      LLStore. 
      apply seqNtoSeq in H14.
      refine (WeakTheory _ _ H14)...
      apply TheoryEmb1.
      
      TFocus (BinBipole IMP_BODY Left F1 G). 
      simpl.
      LLTensor [d| t_bin IMP F1 G | ] (N++x1).
      rewrite H9...
      LLTensor x3 (x++N).
      rewrite <- H10... 
      LLRelease. LLStore.
     apply seqNtoSeq in H11.
     refine (WeakTheory _ _ H11)...
     apply TheoryEmb1.
     
      LLRelease.
      LLStore.  
      PermSwap H14 H8.
      assert(seq (LKC a (pred n)) L ((d| G | :: x) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      LLExact H1.
      
      simpl in H10.
      apply FocusingTensor in H10...
      checkPermutationCases H11.
      
      TFocus (BinBipole IMP_BODY Left F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLTensor (x++N) x4.
      rewrite <- H11... 
      LLRelease. LLStore.
     PermSwap H10 H8.
      assert(seq (LKC a (pred n)) L ((u| F1 | :: x) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
      LLExact H1.
      
      LLRelease.
      LLStore. 
      apply seqNtoSeq in H14.
      refine (WeakTheory _ _ H14)...
      apply TheoryEmb1.
      
      TFocus (BinBipole IMP_BODY Left F1 G). 
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLTensor x3 (x++N).
      rewrite <- H11... 
      LLRelease.
      LLStore. 
      apply seqNtoSeq in H10.
      refine (WeakTheory _ _ H10)...
      apply TheoryEmb1.
      
      LLRelease. LLStore.
     PermSwap H14 H8.
      assert(seq (LKC a (pred n)) L ((d| G | :: x) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      LLExact H1.
   * (* 3/6 - INIT *)  
   apply FocusingInitRuleU in H1...
   checkPermutationCases H7.
   inversion H8...
   apply seqNtoSeq in Hj.
   refine (WeakTheory _ _ Hj)...
   apply TheoryEmb1.
   inversion H7...
   eapply AbsorptionClassic' with (i:=x) (F:=d| OO |)...
   apply allU.
   rewrite <- H9...
   LLStore.
   apply seqNtoSeq in Hj.
   refine (WeakTheory _ _ Hj)...
   apply TheoryEmb1.
   * (* 4/6 - QUANTIFIERS *)  
      inversion H6...
      ** (* 1/4 - ALL Right *)
      apply BipoleReasoning in H1...
      checkPermutationCases H12.
      { inversion H9...
         (** ALL Right is principal *)
          LLrewrite H10 in H11. 
          clear H10.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H13...
                solveF.
                inversion H13...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H12...
                simpl...
                simpl in H13.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H12...
                simpl...
                simpl in H15.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H13... 
                solveF.
                inversion H13... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteANDRight.
                simpl in H15.
                permuteANDRight.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
                permuteANDLeft.
                simpl in H15.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteORRight.  
                simpl in H15.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteORLeft.
                simpl in H15.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteIMPRight.  
                simpl in H15.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.

                apply FocusingTensor in H13...
                rewrite H15 in H10.
                checkPermutationCases H10.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H12...
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H14 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H14)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H17.
      refine (WeakTheory _ _ H17)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H12...
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H14.
      refine (WeakTheory _ _ H14)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H17 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H17)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H13...
                checkPermutationCases H14.
                TFocus (BinBipole IMP_BODY Left F G). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H14...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H10.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                LLRelease. LLStore.
                apply seqNtoSeq in H17.
      refine (WeakTheory _ _ H17)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H14...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H17 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H17)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H9.
             
             inversion H9...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H9...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H12. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H15.
                permuteALLRight.
                solveQF.
                simpl in H16. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
                 { (** CUT-COHERENT CASE *) 
                     inversion H12...
                     rewrite H13.
                     inversion lngF...
                     apply lbindEq in H15...
                     apply lbindEq in H16...
                  
                    eapply GeneralCut' with (C:=dual (ALL_BODY.(rq_leftBody) FX0)).      
               
                    2:{ apply seqNtoSeq in H14.  
                          refine (WeakTheory _ _ H14)...
                          apply TheoryEmb1. }
         
                   rewrite <- (app_nil_l M).
                   
                   eapply GeneralCut' with (C:=dual (ALL_BODY.(rq_rightBody) FX)).
                     
                    2:{ apply seqNtoSeq in H11.
                          refine (WeakTheory _ _ H11)...
                          apply TheoryEmb1. }
                     
                  eapply WeakTheory with (th:=(CUTLN n0)).
                 intros.
                 apply TheoryEmb2.
                 refine(CuteRuleN H5 _)...
                 apply weakeningAll...  
                 apply ALL_CUTCOHERENT...
                 rewrite <- H16...
                 solveUniform.
                 intros...
                 solveQF. }
            
               permuteALLLeft.
               solveQF.
               simpl in H16.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
               permuteSOMERight.
               solveQF.
               simpl in H16.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
               permuteSOMELeft.
               solveQF.
               simpl in H16.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H13.
            
            { inversion H5...
                LLrewrite H10 in H12.
                clear H10.
               apply FocusingQuest in H12...
               eapply AbsorptionL with (i:=a) in Hi.
               eapply CutHC with (n':=n').
               10:{ exact Hi. }
               10:{ exact H10. }
               2:{ eauto. }
               all:sauto.
              }
           
             apply FocusingQuest in H12...
             rewrite H5 in H13.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H10...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H13)...
            apply allU. 
            
            apply FocusingQuest in H12...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H13.
            apply FocusingQuest in H12...
              
             rewrite H5 in H13.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H10...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H13)...
            apply allU. 
            apply FocusingQuest in H12...
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. }      
   
   inversion H11...
   inversion H16...
   solveF.
   Bipole ALL Right FX.
   simpl.
   LLTensor [u| t_quant ALL FX | ] (N++x1).
   rewrite H10...
   LLRelease. 
   LLForall.
   specialize (H19 _ H1).
   inversion H19...
  LLStore.
  PermSwap H22 H9.
      assert(seq (LKC a (pred n)) L ((u| FX x | :: x1) ++ N) (UP [])).
      assert(Heq : n0 + S n1 = n0 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H22 Hj)...
      solveQF. 
      LLExact H13.
      
   inversion H11...
   inversion H16...
   solveF.
   Bipole ALL Right FX.
   simpl.
   LLTensor (@nil oo) (M++N).
   solveLL.
   LLRelease. 
   LLForall.
   specialize (H19 _ H1).
   inversion H19...
  LLStore.
  
      LLSwapL H22.
      assert(seq (LKC a (pred n)) L ((u| FX x | :: M) ++ N) (UP [])).
      assert(Heq : n0 + S n1 = n0 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H22 Hj)...
      solveQF.
      LLExact H12.
      
      ** (* 2/4 - ALL Left *)
      apply BipoleReasoning in H1...
      checkPermutationCases H12. 
      apply FocusingExistsDW in H11...
      Bipole ALL Left FX.
      simpl.
      LLTensor [d| t_quant ALL FX | ] (N++x1).
      rewrite H10...
      LLExists x3.
      LLRelease. LLStore. 
      
      PermSwap H14 H9.
      assert(seq (LKC a (pred n)) L ((d| FX x3 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      solveQF.
      LLExact H1.
      
      apply FocusingExistsDW in H11...
      Bipole ALL Left FX.
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLExists x3. 
      LLRelease. LLStore.
  
      LLSwapL H14.
      assert(seq (LKC a (pred n)) L ((d| FX x3 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      solveQF.
      LLExact H1.
      
      ** (* 3/4 - SOME Right *)
      apply BipoleReasoning in H1...
      checkPermutationCases H12.
     { inversion H9...
         (** SOME Right is principal *)
          LLrewrite H10 in H11. 
          clear H10.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H13...
                solveF.
                inversion H13...
                solveF.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.  
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                rewrite H12...
                simpl...
                simpl in H13.
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H12...
                simpl...
                simpl in H15.
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H13... 
                solveF.
                inversion H13... 
                solveF.     
          - inversion H1...
            (* Connectives Case *) 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteANDRight.
                simpl in H15.
                permuteANDRight.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H14.
                permuteANDLeft.
                simpl in H15.
                permuteANDLeft.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteORRight.  
                simpl in H15.      
                permuteORRight.  
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteORLeft.
                simpl in H15.
                permuteORLeft. 
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.
                permuteIMPRight.  
                simpl in H15.
                
               match goal with 
    | [ H : seqN _ _ _ _ (DW (rb_rightBody _ _)) ,
        Hpp: Permutation ((?i, u| t_bin IMP ?F ?G |) :: ?x) ?Cx
         |- 
        seq _ ?Cx (?M ++ ?N) (UP []) ] => 
        
        apply FocusingPar in H;sauto;
        TFocus (BinBipole IMP_BODY Right F G); 
        simpl;
        LLTensor (@nil oo) (M++N);[
        solveLL |  solveLL;do 2 LLStore;
        rewrite <- PermutConsApp;
            rewrite <-  Permutation_midle;
            rewrite perm_swap
             ]
           
            end.
    
     match goal with
      [C: CutL _ _, 
       HF:  lengthUexp (?P) ?o,
       Hs : seqN ?th ?n ?B (u| ?G | :: d| ?F | :: d| ?P | :: ?x) (UP []),
       Hh : seqN _ ?m _ (u| ?P | :: _) (UP []) |- 
       seq _ _ (_ ++ u| ?G | :: d| ?F | :: ?y) _ ] => 
  let H' := fresh "H" in
    assert(H' : seqN th n B (d| P | :: u| G | :: d| F | ::  x) (UP [])) by LLExact Hs; assert(Heq : m + n = m + n) by auto;
    refine(C _ _ _ _ _ _ _ _ _ _  Heq  _ _ HF _ _ _ _ Hh H');CutTacPOSNEG;OLSolve 
       end.
            -- apply BipoleReasoning in H5...
                checkPermutationCases H14.

                apply FocusingTensor in H13...
                rewrite H15 in H10.
                checkPermutationCases H10.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H12...
                LLTensor (M++x0) x5. 
                rewrite <- H13...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H14 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H14)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H17.
      refine (WeakTheory _ _ H17)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H12...
                LLTensor x4 (M++x0). 
                rewrite <- H13...
                LLRelease. LLStore.
                apply seqNtoSeq in H14.
      refine (WeakTheory _ _ H14)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H17 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H17)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H13...
                checkPermutationCases H14.
                TFocus (BinBipole IMP_BODY Left F G). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H14...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H13 H10.
                
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H13)...
                LLRelease. LLStore.
                apply seqNtoSeq in H17.
      refine (WeakTheory _ _ H17)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H14...
                LLRelease. LLStore.
                apply seqNtoSeq in H13.
      refine (WeakTheory _ _ H13)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                PermSwap H17 H10.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H17)...
          - (* INIT Case *)        
             apply FocusingInitRuleU in H5...
             checkPermutationCases H9.
             
             inversion H9...
             apply seqNtoSeq in Hi.
             rewrite Permutation_midle...
             refine (WeakTheory _ _ Hi)...
             apply TheoryEmb1.
         
             inversion H9...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H12. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - (* Quantifiers Case *)        
            inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H15.
                permuteALLRight.
                solveQF.
                simpl in H16. 
                permuteALLRight.
                solveQF.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
               permuteALLLeft.
               solveQF.
               simpl in H16.
               permuteALLLeft.
               solveQF. 
           -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
               permuteSOMERight.
               solveQF.
               simpl in H16.
               permuteSOMERight.
               solveQF.
           -- apply BipoleReasoning in H5...
               checkPermutationCases H15.
                 { (** CUT-COHERENT CASE *) 
                     inversion H12...
                     rewrite H13.
                     inversion lngF...
                     apply lbindEq in H15...
                     apply lbindEq in H16...
                  
                    eapply GeneralCut' with (C:=dual (SOME_BODY.(rq_leftBody) FX0)).      
               
                    2:{ apply seqNtoSeq in H14.  
                          refine (WeakTheory _ _ H14)...
                          apply TheoryEmb1. }
         
                   rewrite <- (app_nil_l M).
                   
                   eapply GeneralCut' with (C:=dual (SOME_BODY.(rq_rightBody) FX)).
                     
                    2:{ apply seqNtoSeq in H11.
                          refine (WeakTheory _ _ H11)...
                          apply TheoryEmb1. }
                     
                  eapply WeakTheory with (th:=(CUTLN n0)).
                 intros.
                 apply TheoryEmb2.
                 refine(CuteRuleN H5 _)...
                 apply weakeningAll...  
                 apply SOME_CUTCOHERENT...
                 rewrite <- H16...
                 solveUniform.
                 intros...
                 solveQF. } 
                
               permuteSOMELeft.
               solveQF.
               simpl in H16.
               permuteSOMELeft.
               solveQF.
         - (* POS Case *)                    
            apply BipoleReasoning in H5...
            checkPermutationCases H13.
            
            { inversion H5...
                LLrewrite H10 in H12.
                clear H10.
               apply FocusingQuest in H12...
               eapply AbsorptionL with (i:=a) in Hi.
               eapply CutHC with (n':=n').
               10:{ exact Hi. }
               10:{ exact H8. }
               2:{ eauto. }
               all:sauto.
              }
           
             apply FocusingQuest in H12...
             rewrite H5 in H13.
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor [d| OO |] (M++x2).
             rewrite H10...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H13)...
            apply allU. 
            
            apply FocusingQuest in H12...
             eapply weakeningN with (F:=(a, d| OO |)) in Hi...
             TFocus (POS OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU.
         - (* NEG Case *)     
            apply BipoleReasoning in H5...
            checkPermutationCases H13.
            apply FocusingQuest in H12...
              
             rewrite H5 in H13.
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (M++x2).
             rewrite H10...
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H13)...
            apply allU. 
            apply FocusingQuest in H12...
             eapply weakeningN with (F:=(a, u| OO |)) in Hi...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12)...
            apply allU. }      
       
      apply FocusingExistsUP in H11...
      Bipole SOME Right FX.
      simpl.
      LLTensor [u| t_quant SOME FX | ] (N++x1).
      rewrite H10...
      LLExists x3.
      LLRelease. LLStore. 
      
      PermSwap H14 H9.
      assert(seq (LKC a (pred n)) L ((u| FX x3 | :: x1) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      solveQF.
      LLExact H1.
      
      apply FocusingExistsUP in H11...
      Bipole SOME Right FX.
      simpl.
      LLTensor (@nil oo) (M++N).
      solveLL.
      LLExists x3. 
      LLRelease. LLStore.
  
      LLSwapL H14.
      assert(seq (LKC a (pred n)) L ((u| FX x3 | :: M) ++ N) (UP [])).
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H14 Hj)...
      solveQF.
      LLExact H1.   
      
      ** (* 4/4 - SOME Left *)
      apply BipoleReasoning in H1...
      checkPermutationCases H12.
      inversion H11...
      inversion H16...
      solveF.
      Bipole SOME Left FX.
      simpl.
      LLTensor [d| t_quant SOME FX | ] (N++x1).
      rewrite H10...
      LLRelease. 
      LLForall.
      specialize (H19 _ H1).
      inversion H19...
      LLStore.
      PermSwap H22 H9.
      assert(seq (LKC a (pred n)) L ((d| FX x | :: x1) ++ N) (UP [])).
      assert(Heq : n0 + S n1 = n0 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H22 Hj)...
      solveQF. 
      LLExact H13.
      
   inversion H11...
   inversion H16...
   solveF.
   Bipole SOME Left FX.
   simpl.
   LLTensor (@nil oo) (M++N).
   solveLL.
   LLRelease. 
   LLForall.
   specialize (H19 _ H1).
   inversion H19...
  LLStore.
  
      LLSwapL H22.
      assert(seq (LKC a (pred n)) L ((d| FX x | :: M) ++ N) (UP [])).
      assert(Heq : n0 + S n1 = n0 + S n1) by auto.
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H22 Hj)...
      solveQF.
      LLExact H12.
   
   * (* 5/6 - POS *)
      apply BipoleReasoning in H1...
      checkPermutationCases H10.
      apply FocusingQuest in H9...
      rewrite H6 in H10.
   
      TFocus (POS OO a).
      LLTensor [d| OO |] (x1++N).
      rewrite H8...
      LLRelease. LLStoreC.
      eapply weakeningN with (F:=(a, d| OO |) ) in Hj...
      assert(Heq : x2 + S n1 = x2 + S n1) by auto.
  refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
  apply allU.
  
    apply FocusingQuest in H9...
    TFocus (POS OO a).
    LLTensor (@nil oo) (M++N).
    solveLL.
    LLRelease. LLStoreC.
   eapply weakeningN with (F:=(a, d| OO |) ) in Hj...
  assert(Heq : x2 + S n1 = x2 + S n1) by auto.
  refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H9 Hj)...
 apply allU.
 
   * (* 6/6 - NEG *)
      apply BipoleReasoning in H1...
      checkPermutationCases H10.
      { (** NEG is principal *) 
          inversion H6...
          LLrewrite H8 in H9. 
          clear H8.
          inversion H2...
          (* Analizing the derivation on the right *)     
          - (* Constants Case *) 
             inversion H1...
            --  apply BipoleReasoning in H5...
                inversion H11...
                solveF.
                inversion H11...
                solveF.
            -- apply BipoleReasoning in H5...
                simpl in H12.
                checkPermutationCases H12.
                inversion H8...
                { 
               apply FocusingQuest in H9...
               eapply AbsorptionL with (i:=a) in Hj.
               eapply CutHC with (n':=n').
               10:{ exact H9. }
               10:{ exact Hj. }
               2:{ eauto. }
               all:sauto.
              }
            rewrite H10.
                Bipole TT Left.
                LLTensor [d| t_cons TT |] (M++x2). 
                simpl...
                Bipole TT Left.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                simpl in H12.
                checkPermutationCases H12.  
                Bipole FF Right.
                LLTensor [u| t_cons FF |] (M++x2). 
                rewrite H10...
                simpl...
                Bipole FF Right.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                simpl...
            -- apply BipoleReasoning in H5...
                inversion H11... solveF.
                inversion H11... solveF.     
          - inversion H1...
            -- apply BipoleReasoning in H5...
                checkPermutationCases H12.
                permuteANDRight.
                simpl in H13.
                permuteANDRight.
                -- apply BipoleReasoning in H5...
                    checkPermutationCases H12.
                    {
                    inversion H8...
                  
                    apply FocusingQuest in H9... 
                    eapply CutHC with (n':=n') (m:=x2 + S (S x0)).
                    10:{ exact H9. }
                    10:{ apply AbsorptionL...
                            exact Hj. }
                    all:sauto.       
                  }
             
               permuteANDLeft.
               simpl in H13.
               permuteANDLeft.
             -- apply BipoleReasoning in H5...
               checkPermutationCases H12.
               permuteORRight.
               simpl in H13.
               permuteORRight.
            -- apply BipoleReasoning in H5...
               checkPermutationCases H12.
                  {
                    inversion H8...
                  
                    apply FocusingQuest in H9... 
                    eapply CutHC with (n':=n') (m:=x2 + S (S x0)).
                    10:{ exact H9. }
                    10:{ apply AbsorptionL...
                            exact Hj. }
                    all:sauto.       
                  }
             
               
               permuteORLeft.
               simpl in H13.
               permuteORLeft.
               
               -- apply BipoleReasoning in H5...
               checkPermutationCases H12.
               permuteIMPRight.
               
                apply FocusingPar in H11...
                TFocus (BinBipole IMP_BODY Right F G). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. LLRelease.
                LLPar. do 2 LLStore.
                assert(H12' : seqN (LK a) x3 L
        (d| OO | :: u| G | :: d| F | :: N) 
        (UP [])). 
        LLExact H11.
        rewrite <- Permutation_midle.
        rewrite <- Permutation_midle.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ Hi H12')...
            -- apply BipoleReasoning in H5...
               checkPermutationCases H12.
                   {
                    inversion H8...
                  
                    apply FocusingQuest in H9... 
                    eapply CutHC with (n':=n') (m:=x2 + S (S x0)).
                    10:{ exact H8. }
                    10:{ apply AbsorptionL...
                            exact Hj. }
                    all:sauto.       
                  }
             
               
                apply FocusingTensor in H11...
                rewrite H13 in H8.
                checkPermutationCases H8.
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H10...
                LLTensor (M++x0) x5. 
                rewrite <- H11...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                rewrite H8 in H12. 
                LLSwapL H12.
                assert(Heq :S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H12)...
                assert(IsPositiveAtomFormulaL x2)...
                LLRelease. LLStore.
                apply seqNtoSeq in H15.
      refine (WeakTheory _ _ H15)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor [d| t_bin IMP F G | ] (M++x2).
                rewrite H10...
                LLTensor x4 (M++x0). 
                rewrite <- H11...
                LLRelease. LLStore.
                apply seqNtoSeq in H12.
      refine (WeakTheory _ _ H12)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                rewrite H8 in H15. 
                LLSwapL H15.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H15)...
                assert(IsPositiveAtomFormulaL x2)...
                
               apply FocusingTensor in H11...
                checkPermutationCases H12.
                TFocus (BinBipole IMP_BODY Left F G). 
                LLTensor (@nil oo) (M++N).
                solveLL.
                LLTensor (M++x0) x5. 
                rewrite <- H12...
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                rewrite H8 in H11. 
                LLSwapL H11.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H11)...
                LLRelease. LLStore.
                apply seqNtoSeq in H15.
      refine (WeakTheory _ _ H15)...
      apply TheoryEmb1.
      
                TFocus (BinBipole IMP_BODY Left F G). 
                simpl.
                LLTensor (@nil oo) (M++N).
                solveLL. 
                LLTensor x4 (M++x0). 
                rewrite <- H12...
                LLRelease. LLStore.
                apply seqNtoSeq in H11.
      refine (WeakTheory _ _ H11)...
      apply TheoryEmb1.
      
                LLRelease. LLStore.
                rewrite <- Permutation_midle.
                rewrite H8 in H15. 
                LLSwapL H15.
                assert(Heq : S (S x) + x3 = S (S x) + x3) by auto. 
      refine(CutHL _ _ _ _ _ _ _ _ _ _  Heq  _ _ lngF _ _ _ _ Hi H15)... 
      - apply FocusingInitRuleU in H5...
         checkPermutationCases H6.
         inversion H6...
         apply seqNtoSeq in Hi.
         rewrite Permutation_midle...
        
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         
         inversion H6...
         eapply AbsorptionClassic with (i:=x0).
         3:{ rewrite <- H10. left. eauto. }
         apply allU. auto.
         simpl... LLStore.
        
         apply seqNtoSeq in Hi.
         refine (WeakTheory _ _ Hi)...
         apply TheoryEmb1.
         - inversion H1...
              -- 
                apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteALLRight.
                solveQF.
                simpl in H14.
                permuteALLRight.
                solveQF.
              -- 
                apply BipoleReasoning in H5...
                checkPermutationCases H13.
                  {
                    inversion H10...
                  
                    apply FocusingQuest in H9... 
                    eapply CutHC with (n':=n') (m:=x2 + S (S x0)).
                    10:{ exact H10. }
                    10:{ apply AbsorptionL...
                            exact Hj. }
                    all:sauto.       
                  }
             
                permuteALLLeft.
                solveQF.
                simpl in H14.
                permuteALLLeft.
                solveQF.
              -- 
                apply BipoleReasoning in H5...
                checkPermutationCases H13.
                permuteSOMERight.
                solveQF.
                simpl in H14.
                permuteSOMERight.
                solveQF.
              -- 
                apply BipoleReasoning in H5...
                checkPermutationCases H13.
                      {
                    inversion H10...
                  
                    apply FocusingQuest in H9... 
                    eapply CutHC with (n':=n') (m:=x2 + S (S x0)).
                    10:{ exact H9. }
                    10:{ apply AbsorptionL...
                            exact Hj. }
                    all:sauto.       
                  }
            
                permuteSOMELeft.
                solveQF.
                simpl in H14.
                permuteSOMELeft.
                solveQF.
             
  -  apply BipoleReasoning in H5...
             checkPermutationCases H11.
             
             inversion H5...
             apply FocusingQuest in H9...
             apply FocusingQuest in H10...
             rewrite H8.
              assert(Heq : x2 + x = x2 + x) by auto. 
      refine(CutHC _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H7 H9)...
       
            apply FocusingQuest in H10...
            apply FocusingQuest in H9...
                 TFocus (POS OO0 a).
       LLTensor [d| OO0 |] (M++x2).
       rewrite H8...
       LLRelease. LLStoreC.
       eapply CutHL with (n':=n') (m:= S (S (S (S x0))) + x3). 
       10:{ apply weakeningN. 
               simpl... apply allU. 
               exact Hi. }
       10:{  rewrite <- H5.
                 exact H11. }
        all: simpl...                
         
            apply FocusingQuest in H10...
            apply FocusingQuest in H9...
                 TFocus (POS OO0 a).
       LLTensor (@nil oo) (M++N).
       solveLL.
       LLRelease. LLStoreC.
       eapply CutHL with (n':=n') (m:= S (S (S (S x0))) + x3). 
       10:{ apply weakeningN. 
               simpl... apply allU. 
               exact Hi. }
       10:{  exact H10. }
        all: simpl...                
   -  apply BipoleReasoning in H5...
       checkPermutationCases H11.
       apply FocusingQuest in H10...
       apply FocusingQuest in H9...
       
          TFocus (NEG OO0 a).
       LLTensor [u| OO0 |] (M++x2).
       rewrite H8...
       LLRelease. LLStoreC.
       eapply CutHL with (n':=n') (m:= S (S (S (S x0))) + x3). 
       10:{ apply weakeningN. 
               simpl... apply allU. 
               exact Hi. }
       10:{  rewrite <- H5.
                 exact H11. }
        all: simpl...                
       
            apply FocusingQuest in H10...
            apply FocusingQuest in H9...
                 TFocus (NEG OO0 a).
       LLTensor (@nil oo) (M++N).
       solveLL.
       LLRelease. LLStoreC.
       eapply CutHL with (n':=n') (m:= S (S (S (S x0))) + x3). 
       10:{ apply weakeningN. 
               simpl... apply allU. 
               exact Hi. }
       10:{  exact H10. }
        all: simpl... }
            apply FocusingQuest in H9...
               rewrite H6 in H10.
             eapply weakeningN with (F:=(a, u| OO |)) in Hj...
             TFocus (NEG OO a).  
             LLTensor [u| OO |] (x1++N).
             rewrite H8...
             LLRelease. LLStoreC.
            assert(Heq : x2 + (S n1) = x2 + (S n1)) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H10 Hj)...
            apply allU. 
            
            apply FocusingQuest in H9...
             eapply weakeningN with (F:=(a, u| OO |)) in Hj...
             TFocus (NEG OO a).  
             LLTensor (@nil oo) (M++N).
             solveLL.
             LLRelease. LLStoreC.
            assert(Heq : x2 + (S n1) = x2 + (S n1)) by auto. 
      
             refine(CutHL _ _ _ _ _ _ _ _ _ _ Heq  _ _ lngF _ _ _ _ H9 Hj)...
            apply allU. 
Qed.

End LKCutL.