(*
* Arian van Putten 4133935
* Adolfo Ochagavia 4045483
*)

(* libraries *)
load "intLib" ;
open intLib ;
load "stringLib" ;
open stringLib ;
load "stringSimps" ;
open stringSimps ;

Hol_datatype
   `GCL = SKIP
        | ASSUME of 'pred
        | SEQ    of GCL => GCL
        | ASG    of string => 'expr
   ` ;

val SEQS_def   = Define `(SEQS [] = SKIP) /\ (SEQS (S1::rest) = SEQ S1 (SEQS rest))` ;

val exec_def = Define
       `(exec SKIP s t = (s=t))  (* t is a final state of SKIP s, if and only if t=s *)
         /\
        (exec (ASSUME p) s t = p s /\ (s=t))
         /\
        (exec (SEQ S1 S2) s u = (?t. exec S1 s t /\ exec S2 t u))
        /\
        (exec (ASG v e) s t = (t = (\var. if var=v then e s else s var)))
        ` ;

val HOARE_def = Define `HOARE gcl p q = (!s t. p s /\ exec gcl s t ==> q t)` ;

val TT_def  = Define `TT = (\s. T)` ;
val FF_def  = Define `FF = (\s. F)` ;
val NOT_def = Define `NOT g = (\s. ~g s)` ;
val IMP_def = Define `IMP p q = (\s. p s ⇒ q s)`;
val AND_def = Define `AND p q = (\s. p s ∧ q s)`;
val VALID_def = Define  `VALID p = (∀s. p s)`;


val HOARE_precond_strengthening_thm = prove
   (--`VALID (IMP p1 p2) /\ HOARE stmt p2 q ==> HOARE stmt p1 q`--,
    REWRITE_TAC [VALID_def, IMP_def]
    THEN REWRITE_TAC [HOARE_def]
    THEN BETA_TAC (* Added extra BETA_TAC *)
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC [] ) ;


val HOARE_postcond_weakening_thm = prove
  (--`VALID (IMP q1 q2) ∧ HOARE stmt p q1 ⇒ HOARE stmt p q2 `--,
  REWRITE_TAC [VALID_def, IMP_def]
  THEN REWRITE_TAC [HOARE_def]
  THEN BETA_TAC (* Added extra BETA_TAC *)
  THEN REPEAT STRIP_TAC
  THEN PROVE_TAC []
  );


val wlp_def = Define
       `(wlp SKIP q = q)
         /\
        (wlp (ASSUME p) q  = (\s. p s ==> q s))
         /\
        (wlp (SEQ S1 S2) q = wlp S1 (wlp S2 q))
        /\
        (wlp (ASG v e) q  = (\s. q (\var. if var=v then e s else s var)))
        ` ;



val SOUND_wlp_skip_thm = prove
    (--`HOARE SKIP (wlp SKIP q) q`--,
    REWRITE_TAC [HOARE_def]
    THEN REWRITE_TAC [wlp_def]
    THEN REWRITE_TAC [exec_def]
    THEN BETA_TAC
    THEN PROVE_TAC []
    ) ;

val SOUND_wlp_assume_thm = prove
    (--`HOARE (ASSUME p) (wlp (ASSUME p) q) q`--,
    REWRITE_TAC [HOARE_def]
    THEN REWRITE_TAC [wlp_def]
    THEN REWRITE_TAC [exec_def]
    THEN BETA_TAC
    THEN PROVE_TAC []
    );


val SOUND_wlp_asg_thm = prove
    (--`HOARE (ASG v e) (wlp (ASG v e) q) q`--,
    REWRITE_TAC [HOARE_def]
    THEN REWRITE_TAC [wlp_def]
    THEN REWRITE_TAC [exec_def]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
    );

val SOUND_wlp_seq_thm = prove
    (--`HOARE S1 p q ∧ HOARE S2 q r ⇒ HOARE (SEQ S1 S2) p r`--,
    REWRITE_TAC [HOARE_def]
    THEN REWRITE_TAC [wlp_def]
    THEN REWRITE_TAC [exec_def]
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC []
    );


(* quantify *)
val lol = GEN_ALL(SOUND_wlp_seq_thm);


(* Oh it's because we need the same amount of arguments in THENL
* that the Induct_on returns  => *)

val SOUND_wlp_thm = prove
   (--`(!q. HOARE gcl (wlp gcl q) q)`--,
    Induct_on `gcl`
    THENL
    [ PROVE_TAC [SOUND_wlp_skip_thm],
      PROVE_TAC [SOUND_wlp_assume_thm],

      STRIP_TAC
        THEN MATCH_MP_TAC lol
        THEN REWRITE_TAC [wlp_def]
        THEN EXISTS_TAC (--`wlp gcl' q`--)
        THEN ASM_REWRITE_TAC[],

      PROVE_TAC [SOUND_wlp_asg_thm]
    ]
  ) ;
