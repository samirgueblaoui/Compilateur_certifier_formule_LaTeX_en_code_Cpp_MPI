From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C00_Source.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Syntaxe des expressions de la machine cible. *)
Inductive exprCible : Type :=
| ACstEnt : Z -> exprCible
| ACstFlot : R -> exprCible
| ABool : bool -> exprCible
| AVar : var -> exprCible
| APrimUn : opUn -> exprCible -> exprCible
| APlus : exprCible -> exprCible -> exprCible
| AMult : exprCible -> exprCible -> exprCible
| AMoins : exprCible -> exprCible -> exprCible
| AMod : exprCible -> exprCible -> exprCible
| APrimBin : opBinPrim -> exprCible -> exprCible -> exprCible
| AInfEg : exprCible -> exprCible -> exprCible
| AEg : exprCible -> exprCible -> exprCible
| ANon : exprCible -> exprCible
| AEt : exprCible -> exprCible -> exprCible
| ANbGroupes : exprCible -> exprCible
| ATailleGroupe : exprCible -> exprCible -> exprCible
| ACouleur : exprCible -> exprCible -> exprCible -> exprCible
| ARangEnfant : exprCible -> exprCible -> exprCible -> exprCible
| ATailleEnfant : exprCible -> exprCible -> exprCible -> exprCible.

(** Contexte *)
Record ctx : Type := {
  ctxRang : var;
  ctxNbProc : var;
  ctxActif : exprCible;
  ctxNiveau : nat;
  ctxRepr : var -> var
}.

(** Contexte initial *)
Definition ctx0 : ctx :=
  {| ctxRang := "rang";
     ctxNbProc := "nbProc";
     ctxActif := ABool true;
     ctxNiveau := 0%nat;
     ctxRepr := fun x => x |}.

(** Associe une variable source à une variable cible. *)
Definition lierVarCtx (c : ctx) (x z : var) : ctx :=
  {| ctxRang := ctxRang c;
     ctxNbProc := ctxNbProc c;
     ctxActif := ctxActif c;
     ctxNiveau := ctxNiveau c;
     ctxRepr := fun y =>
       if String.eqb y x then z else ctxRepr c y |}.

(** Construit le contexte d'un groupe enfant. *)
Definition ctxEnfant
  (c : ctx) (rangEnfant tailleEnfant couleur groupeResp : var) : ctx :=
  {| ctxRang := rangEnfant;
     ctxNbProc := tailleEnfant;
     ctxActif :=
       AEt (ctxActif c) (AEg (AVar couleur) (AVar groupeResp));
     ctxNiveau := S (ctxNiveau c);
     ctxRepr := ctxRepr c |}.

(** Syntaxe des commandes de la machine cible. *)
Inductive cmd : Type :=
| CRien
| CAffect : var -> exprCible -> cmd
| CSeq : cmd -> cmd -> cmd
| CSi : exprCible -> list var -> cmd -> list var -> cmd -> cmd
| CPour : cmd -> exprCible -> cmd -> list var -> cmd -> cmd
| CRedTous : var -> var -> cmd.

Inductive cadre : Type :=
| KCmd : cmd -> cadre
| KEff : list var -> cadre.

(** Pile de continuation d'un processus. *)
Definition cont := list cadre.

(** État local d'un processus cible. *)
Record etatLoc : Type := {
  elMem : mem;
  elCont : cont
}.

(** Configuration globale de tous les processus. *)
Definition configGlob := list etatLoc.

(** Code, résultat, type et fraîcheur produits par la compilation. *)
Record resComp : Type := {
  rcCode : cmd;
  rcRes : var;
  rcType : typeNum;
  rcProchain : nat
}.

(** Encode un entier naturel dans un nom. *)
Fixpoint nomNat (n : nat) : string :=
  match n with
  | O => "0"
  | S n' => "S" ++ nomNat n'
  end.

(** Construit le nom d'une variable temporaire. *)
Definition nomTemp (n : nat) : var :=
  "tmp" ++ nomNat n.

(** Expression cible représentant le zéro d'un type. *)
Definition exprNulle (t : typeNum) : exprCible :=
  match t with
  | TEnt => ACstEnt 0
  | TFlot => ACstFlot 0
  end.

(** Met une liste de commandes en séquence. *)
Fixpoint seqCmds (cs : list cmd) : cmd :=
  match cs with
  | [] => CRien
  | [c] => c
  | c :: suite => CSeq c (seqCmds suite)
  end.

(** Énumère variables temporaires. *)
Fixpoint nomsTempDepuis (debut nb : nat) : list var :=
  match nb with
  | O => []
  | S nb' => nomTemp debut :: nomsTempDepuis (S debut) nb'
  end.

(** Énumère les temporaires entre deux indices. *)
Definition nomsTempEntre (debut fin : nat) : list var :=
  nomsTempDepuis debut (fin - debut).

(** Traduit une opération binaire en expression cible. *)
Definition exprBinCible
  (op : formeBin) (x y : var) : exprCible :=
  match op with
  | BPlus => APlus (AVar x) (AVar y)
  | BMult => AMult (AVar x) (AVar y)
  | BPrim f => APrimBin f (AVar x) (AVar y)
  end.

(** Compile récursivement une expression source. *)
Fixpoint comp
  (e : expr) (Gamma : envTypes)
  (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (frais : nat) : resComp :=
  match e with
  | ECstEnt n =>
      {| rcCode := CAffect (nomTemp frais) (ACstEnt n);
         rcRes := nomTemp frais;
         rcType := TEnt;
         rcProchain := S frais |}
  | ECstFlot r =>
      {| rcCode := CAffect (nomTemp frais) (ACstFlot r);
         rcRes := nomTemp frais;
         rcType := TFlot;
         rcProchain := S frais |}
  | EVar x =>
      {| rcCode := CRien;
         rcRes := ctxRepr ctxComp x;
         rcType :=
           match Gamma x with
           | Some t => t
           | None => TEnt
           end;
         rcProchain := frais |}
  | EUn op e1 =>
      let r1 := comp e1 Gamma U B ctxComp frais in
      let dest := nomTemp (rcProchain r1) in
      {| rcCode :=
           seqCmds
             [rcCode r1;
              CAffect dest (APrimUn op (AVar (rcRes r1)))];
         rcRes := dest;
         rcType := typeResUn U op (rcType r1);
         rcProchain := S (rcProchain r1) |}
  | EBin op e1 e2 =>
      let r1 := comp e1 Gamma U B ctxComp frais in
      let r2 :=
        comp e2 Gamma U B ctxComp (rcProchain r1) in
      let dest := nomTemp (rcProchain r2) in
      {| rcCode :=
           seqCmds
             [rcCode r1;
              rcCode r2;
              CAffect dest
                (exprBinCible op (rcRes r1) (rcRes r2))];
         rcRes := dest;
         rcType :=
           typeResBin B op (rcType r1) (rcType r2);
         rcProchain := S (rcProchain r2) |}
  | ESomSeq i a b corps =>
      let ra := comp a Gamma U B ctxComp frais in
      let rb :=
        comp b Gamma U B ctxComp (rcProchain ra) in
      let acc := nomTemp (rcProchain rb) in
      let ind := nomTemp (S (rcProchain rb)) in
      let debutCorps := S (S (rcProchain rb)) in
      let ctxCorps := lierVarCtx ctxComp i ind in
      let ru :=
        comp corps (lierTypeEnt Gamma i) U B
          ctxCorps debutCorps in
      {| rcCode :=
           seqCmds
             [rcCode ra;
              rcCode rb;
              CAffect acc (exprNulle (rcType ru));
              CPour
                (CAffect ind (AVar (rcRes ra)))
                (AInfEg (AVar ind) (AVar (rcRes rb)))
                (CAffect ind (APlus (AVar ind) (ACstEnt 1)))
                (nomsTempEntre debutCorps (rcProchain ru))
                (seqCmds
                   [rcCode ru;
                    CAffect acc
                      (APlus (AVar acc) (AVar (rcRes ru)))])];
         rcRes := acc;
         rcType := rcType ru;
         rcProchain := rcProchain ru |}
  | ESomPar i a b corps =>
      let ra := comp a Gamma U B ctxComp frais in
      let rb :=
        comp b Gamma U B ctxComp (rcProchain ra) in
      let nf := rcProchain rb in
      if contientSomPar corps then
        let nbGroupes := nomTemp nf in
        let tailleGroupe := nomTemp (S nf) in
        let couleur := nomTemp (S (S nf)) in
        let rangEnfant := nomTemp (S (S (S nf))) in
        let tailleEnfant := nomTemp (S (S (S (S nf)))) in
        let groupeResp := nomTemp (S (S (S (S (S nf))))) in
        let acc := nomTemp (S (S (S (S (S (S nf)))))) in
        let ind := nomTemp (S (S (S (S (S (S (S nf))))))) in
        let debutCorps := S (S (S (S (S (S (S (S nf))))))) in
        let enfant :=
          ctxEnfant ctxComp rangEnfant tailleEnfant couleur groupeResp in
        let ctxCorps := lierVarCtx enfant i ind in
        let ru :=
          comp corps (lierTypeEnt Gamma i) U B
            ctxCorps debutCorps in
        let res := nomTemp (rcProchain ru) in
        {| rcCode :=
             seqCmds
               [rcCode ra;
                rcCode rb;
                CAffect nbGroupes (ANbGroupes (AVar (ctxNbProc ctxComp)));
                CAffect tailleGroupe
                  (ATailleGroupe (AVar (ctxNbProc ctxComp)) (AVar nbGroupes));
                CAffect couleur
                  (ACouleur (AVar (ctxRang ctxComp))
                    (AVar tailleGroupe) (AVar nbGroupes));
                CAffect rangEnfant
                  (ARangEnfant (AVar (ctxRang ctxComp))
                    (AVar couleur) (AVar tailleGroupe));
                CAffect tailleEnfant
                  (ATailleEnfant (AVar (ctxNbProc ctxComp))
                    (AVar couleur) (AVar tailleGroupe));
                CAffect acc (exprNulle (rcType ru));
                CPour
                  (CAffect ind (AVar (rcRes ra)))
                  (AInfEg (AVar ind) (AVar (rcRes rb)))
                  (CAffect ind (APlus (AVar ind) (ACstEnt 1)))
                  (nomsTempEntre debutCorps (rcProchain ru))
                  (seqCmds
                    [CAffect groupeResp
                       (AMod
                         (APlus
                           (AMod
                             (AMoins (AVar ind) (AVar (rcRes ra)))
                             (AVar nbGroupes))
                           (AVar nbGroupes))
                         (AVar nbGroupes));
                     rcCode ru;
                     CSi
                       (AEt
                         (AEt (ctxActif ctxComp)
                           (AEg (AVar couleur) (AVar groupeResp)))
                         (AEg (AVar rangEnfant) (ACstEnt 0)))
                       []
                       (CAffect acc
                         (APlus (AVar acc) (AVar (rcRes ru))))
                       [] CRien]);
                CAffect res (exprNulle (rcType ru));
                CRedTous acc res];
           rcRes := res;
           rcType := rcType ru;
           rcProchain := S (rcProchain ru) |}
      else
        let acc := nomTemp nf in
        let ind := nomTemp (S nf) in
        let debutCorps := S (S nf) in
        let ctxCorps := lierVarCtx ctxComp i ind in
        let ru :=
          comp corps (lierTypeEnt Gamma i) U B
            ctxCorps debutCorps in
        let res := nomTemp (rcProchain ru) in
        {| rcCode :=
             seqCmds
               [rcCode ra;
                rcCode rb;
                CAffect acc (exprNulle (rcType ru));
                CSi (ctxActif ctxComp) []
                  (CPour
                    (CAffect ind
                      (APlus (AVar (rcRes ra))
                        (AVar (ctxRang ctxComp))))
                    (AInfEg (AVar ind) (AVar (rcRes rb)))
                    (CAffect ind
                      (APlus (AVar ind) (AVar (ctxNbProc ctxComp))))
                    (nomsTempEntre debutCorps (rcProchain ru))
                    (seqCmds
                      [rcCode ru;
                       CAffect acc
                         (APlus (AVar acc) (AVar (rcRes ru)))]))
                  [] CRien;
                CAffect res (exprNulle (rcType ru));
                CRedTous acc res];
           rcRes := res;
           rcType := rcType ru;
           rcProchain := S (rcProchain ru) |}
  end.
