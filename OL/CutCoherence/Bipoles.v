Require Export MMLL.OL.CutCoherence.OLTactics.
Require Export MMLL.OL.CutCoherence.OLPosNeg.


Set Implicit Arguments.

Section Bipoles.

Context {SI : Signature}.
Context {SY : OLSyntax}.

Class BinBody: Set
  :=
  { con: connectives;
     rb_rightBody : uexp -> uexp -> oo;
     rb_leftBody : uexp -> uexp -> oo}.

Class UnBody: Set
  :=
  { ucon: uconnectives;
     ru_rightBody : uexp -> oo;
     ru_leftBody : uexp -> oo}.

Class CteBody: Set
  :=
  { cte : constants;
     rc_rightBody : oo;
     rc_leftBody : oo}.

Class QuBody : Set 
  :=
    {qt : quantifiers;
    rq_rightBody : (uexp -> uexp) -> oo; 
      rq_leftBody :  (uexp -> uexp) -> oo }.
    
 Class BinCutCoherent `(Bin : BinBody) {RCUT} :=    
   {    BBCut_coherent n F m G:  
         lengthUexp F n ->
         lengthUexp G m ->
         isOLFormula F -> 
         isOLFormula G->
         seq (RCUT (max n m)) [] [] (UP [dual (rb_rightBody F G) ; dual (rb_leftBody F G)])
  }.  

 Class UnCutCoherent `(Un : UnBody) {RCUT} :=    
   {   UBCut_coherent n F:  
         lengthUexp F n ->
         isOLFormula F -> 
         seq (RCUT n) [] [] (UP [dual (ru_rightBody F) ; dual (ru_leftBody F)])
  }.
  
 Class QuCutCoherent `(Qu : QuBody) {RCUT} :=    
   {   QUCut_coherent n FX FX':  
        uniform FX ->
        uniform FX' ->
        ext_eq FX FX' ->
        lengthUexp (FX (Var 0%nat))  n ->
    (forall t, proper t -> isOLFormula (FX t)) ->
         seq (RCUT n) [] [] (UP [dual (rq_rightBody FX) ; dual (rq_leftBody FX')]) }.  

Class CteCutCoherent `(Qu : CteBody) :=    
   {   COCut_coherent:  
         seq EmptyTheory [] [] (UP [dual (rc_rightBody) ; dual (rc_leftBody)]) }.
         
  (** building rules for connectives *)
   Definition BinBipole  (Bi: BinBody) (s:Side):=
    fun (A B :uexp) =>
      match s with
      | Right => MAnd (u^| t_bin con A B|) (rb_rightBody A B)
      | Left => MAnd (d^| t_bin con A B|) (rb_leftBody A B)
      end.

   Definition UnBipole  (Bi: UnBody) (s:Side):=
    fun (A:uexp) =>
      match s with
      | Right => MAnd (u^| t_ucon ucon A |) (ru_rightBody A)
      | Left => MAnd (d^| t_ucon ucon A |) (ru_leftBody A)
      end.

  (** building rules for constants *)
  Definition CteBipole (Cte: CteBody) (s:Side) :=
    match s with
    | Right => MAnd ( u^|t_cons cte | ) (rc_rightBody)
    | Left => MAnd ( d^|t_cons cte| ) (rc_leftBody)
    end.
  
   (** building rules for quantifiers *)
  Definition QuBipole (Qu: QuBody) (s:Side):=
    fun (FX :uexp -> uexp) =>
      match s with
      | Right => MAnd (u^| t_quant qt FX|) (rq_rightBody FX)
      | Left => MAnd (d^| t_quant qt FX|) (rq_leftBody FX)
      end.

 (** INIT and CUT rules *)
  Definition RINIT (F:uexp) := 
          MAnd (u^| F |)  (d^| F |) .

  Definition CUTL F :=  
          MAnd (d| F |)  (u| F |).
          
  Definition CUTC a F := 
          MAnd (Quest a (d| F |)) (Quest a (u| F |)).

  Inductive CUTLN (n:nat) : oo -> Prop :=
  | ltn : forall (F:uexp) m, isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CUTLN n (CUTL F).
  
  Inductive CUTCN {a:subexp} (n:nat) : oo -> Prop :=                            
  | ctn : forall (F:uexp) m, isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CUTCN n (CUTC a F).           
End Bipoles.           

