
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
        | IFTHENELSE of 'pred => GCL => GCL
        | WHILE of 'pred => 'pred => GCL
   ` ;

val SEQS_def   = Define `(SEQS [] = SKIP) /\ (SEQS (S1::rest) = SEQ S1 (SEQS rest))` ;


val iter_def = Define
    `(iter g body 0 s t = ~g s /\ (t=s))
      /\
      (iter g body (SUC k) s t = (g s /\ (?s'. body s s' /\ iter g body k s' t)))` ;

val exec_def = Define
       `(exec SKIP s t = (s=t))  (* t is a final state of SKIP s, if and only if t=s *)
         /\
        (exec (ASSUME p) s t = p s /\ (s=t))
         /\
        (exec (SEQ S1 S2) s u = (?t. exec S1 s t /\ exec S2 t u))
        /\
        (exec (ASG v e) s t = (t = (\var. if var=v then e s else s var)))
        ∧
        (exec (IFTHENELSE g S1 S2) s t = (g s ⇒ exec S1 s t) ∧ (¬g s ⇒ exec S2 s t))
        ∧
        (exec (WHILE inv g body) s t = (?k. iter g (exec body) k s t))
        ` ;

val HOARE_def = Define `HOARE gcl p q = (∀ s t. p s ∧ exec gcl s t ⇒   q t)` ;

val TT_def  = Define `TT = (\s. T)` ;
val FF_def  = Define `FF = (\s. F)` ;
val NOT_def = Define `NOT g = (\s. ~g s)` ;
val IMP_def = Define `IMP p q = (\s. p s ⇒ q s)`;
val AND_def = Define `AND p q = (\s. p s ∧ q s)`;
val OR_def = Define `OR p q = (\s. p s \/ q s)`;
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

val HOARE_triple_disjunction = prove
    (--`HOARE s p1 q1 ∧ HOARE s p2 q2 ⇒ HOARE s (OR p1 p2) (OR q1 q2)`--,
    REWRITE_TAC [HOARE_def, OR_def]
    THEN PROVE_TAC[]
    );

val HOARE_triple_conjunction = prove
    (--`HOARE s p1 q1 ∧ HOARE s p2 q2 ⇒ HOARE s (AND p1 p2) (AND q1 q2)`--,
    REWRITE_TAC [HOARE_def, AND_def]
    THEN PROVE_TAC[]
    );

val HOARE_seq_thm = prove
    (--`HOARE S1 p q ∧ HOARE S2 q r ⇒ HOARE (SEQ S1 S2) p r`--,
    REWRITE_TAC [HOARE_def]
    THEN REWRITE_TAC [exec_def]
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC []
    );


val HOARE_if_then_else1_thm = prove
    ( --`HOARE S1 (AND p g) q ∧ HOARE S2 (AND p (NOT g)) q ⇒ HOARE (IFTHENELSE g S1 S2) p q`--,
    REWRITE_TAC[HOARE_def, AND_def, NOT_def, exec_def]
    THEN PROVE_TAC[]
    );

val HOARE_if_then_else_2_thm = prove
    (--`HOARE S1 p1 q ∧ HOARE S2 p2 q ⇒ HOARE (IFTHENELSE g S1 S2) (AND (IMP g p1) (IMP (NOT g) p2)) q`--,
    REWRITE_TAC[HOARE_def, AND_def, IMP_def, NOT_def, exec_def]
    THEN PROVE_TAC[]
    );


val HOARE_loop_thm1 = prove
    (--`(HOARE (WHILE inv' g body) (AND (NOT g) q) q)`--,
    REWRITE_TAC[HOARE_def, AND_def, NOT_def]
    THEN BETA_TAC
    THEN REWRITE_TAC [exec_def]
    THEN REPEAT STRIP_TAC
    THEN Cases_on `k`
    THENL
    [ FULL_SIMP_TAC std_ss [iter_def]
    , RULE_ASSUM_TAC (REWRITE_RULE [iter_def]) (* now we have contradiction *)
      THEN PROVE_TAC[]
    ]
    );


val lemma = prove(--`p ==> q ==> r = (p /\ q) ==> r`--, PROVE_TAC[]);

val HOARE_loop_lemma1 = prove
    (--`HOARE body (AND inv' g) inv' ⇒ HOARE (WHILE inv' g body) inv' (AND inv' (NOT g)) `--,
    REWRITE_TAC[HOARE_def, AND_def, NOT_def]
    THEN BETA_TAC
    THEN REWRITE_TAC[exec_def]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN FIRST_ASSUM (UNDISCH_TAC o concl)
    THEN FIRST_ASSUM (UNDISCH_TAC o concl)
    THEN SPEC_TAC (--`s: string -> 'a`--, --`s: string-> 'a`--)
    THEN SPEC_TAC (--`t: string -> 'a`--, --`t: string-> 'a`--)
    THEN Induct_on `k`
    THENL [
      REWRITE_TAC[iter_def]
      THEN PROVE_TAC[],
      REWRITE_TAC[iter_def]
      THEN PROVE_TAC[]
      (* OR:
      Magic I did with Wishnu, however cannot reproduce,
      will try later.
      THEN STRIP_TAC (* now PROVE_TAC[], OR manually *)
      THEN STRIP_TAC
      THEN STRIP_TAC
      THEN FIRST_ASSUM (MATCH_MP_TAC)
      THEN RULE_ASSUM_TAC (REWRITE_RULE [lemma])
      THEN FIRST_ASSUM (MATCH_MP_TAC)
      THEN EXISTS_TAC (--`s' : string -> 'a`--)
      THEN ASM_REWRITE_TAC[]
      THEN FIRST_ASSUM MATCH_MP_TAC
      THEN EXISTS_TAC (--`s : string -> 'a`--)
      THEN ASM_REWRITE_TAC[]*)
    ]
    );



val HOARE_loop_thm_2 = prove
    (--`VALID (IMP p inv') /\ HOARE S' (AND inv' g) (inv') ∧ VALID (IMP (AND (inv') (NOT g)) q) ⇒ HOARE (WHILE inv' g S') p q`--,
    STRIP_TAC
    THEN MATCH_MP_TAC (GEN_ALL HOARE_postcond_weakening_thm)
    THEN EXISTS_TAC(--`AND inv' (NOT g) : (string -> 'a) -> bool`--)
    THEN CONJ_TAC
    THENL
    [ ASM_REWRITE_TAC[]
    , MATCH_MP_TAC (GEN_ALL HOARE_precond_strengthening_thm)
      THEN EXISTS_TAC(--`inv' : (string -> 'a) -> bool`--)
      THEN ASM_REWRITE_TAC[]
      THEN MATCH_MP_TAC(GEN_ALL(HOARE_loop_lemma1))
      THEN ASM_REWRITE_TAC[]
    ]
    );

val HOARE_asg_thm = prove
      (--`HOARE (ASG v e) (\s. q (\var. if var=v then e s else s var)) q `--,
      REWRITE_TAC[HOARE_def]
      THEN REWRITE_TAC[exec_def]
      THEN BETA_TAC
      THEN REPEAT STRIP_TAC
      THEN ASM_REWRITE_TAC[]
      );

val wlp_def = Define
       `(wlp SKIP q = q)
        ∧
        (wlp (ASSUME p) q  = (\s. p s ⇒ q s))
        ∧
        (wlp (SEQ S1 S2) q = wlp S1 (wlp S2 q))
        ∧
        (wlp (ASG v e) q  = (\s. q (\var. if var=v then e s else s var)))
        ∧
        (wlp (IFTHENELSE g S1 S2) q =
          (λs. (g s ⇒ wlp S1 q s) ∧ (¬(g s) ⇒ wlp S2 q s)))
        ∧
        (wlp (WHILE inv' g S') q =
          if VALID (IMP (AND inv' (NOT g)) q) ∧ VALID (IMP (AND inv' g) (wlp S' inv'))
          then inv'
          else AND (NOT g) q
        )
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




(* Oh it's because we need the same amount of arguments in THENL
* that the Induct_on returns  => *)


(* we need this for lulz . lifted lemma1*)
val lemma2 = prove(--`IMP (p) (IMP q r) = IMP (AND p q) r`--, REWRITE_TAC[IMP_def,AND_def] THEN BETA_TAC THEN PROVE_TAC[]);


val SOUND_wlp_thm = prove
   (--`(!q. HOARE gcl (wlp gcl q) q)`--,
    Induct_on `gcl`
    THENL
    [ PROVE_TAC [SOUND_wlp_skip_thm],
      PROVE_TAC [SOUND_wlp_assume_thm],

      STRIP_TAC
        THEN MATCH_MP_TAC (GEN_ALL(HOARE_seq_thm))
        THEN REWRITE_TAC [wlp_def]
        THEN EXISTS_TAC (--`wlp gcl' q`--)
        THEN ASM_REWRITE_TAC[],


      PROVE_TAC [SOUND_wlp_asg_thm],

      STRIP_TAC
        THEN STRIP_TAC
        THEN MATCH_MP_TAC(GEN_ALL(HOARE_if_then_else1_thm))
        THEN CONJ_TAC
        THENL
        [ MATCH_MP_TAC(GEN_ALL(HOARE_precond_strengthening_thm))
            THEN EXISTS_TAC (--`(wlp gcl q)`--)
            THEN ASM_REWRITE_TAC []
            THEN REWRITE_TAC[VALID_def, IMP_def, AND_def, wlp_def]
            THEN BETA_TAC
            THEN PROVE_TAC[]
        , MATCH_MP_TAC(GEN_ALL(HOARE_precond_strengthening_thm))
            THEN EXISTS_TAC (--`(wlp gcl' q)`--)
            THEN ASM_REWRITE_TAC []
            THEN REWRITE_TAC[VALID_def, IMP_def, NOT_def, AND_def, wlp_def]
            THEN BETA_TAC
            THEN PROVE_TAC[]
        ]
      REPEAT STRIP_TAC
      THEN REWRITE_TAC[wlp_def]
      THEN IF_CASES_TAC
      THENL
      [ MATCH_MP_TAC(GEN_ALL(HOARE_loop_thm_2))
        THEN ASM_REWRITE_TAC[]
        THEN CONJ_TAC
        THENL
        [ PROVE_TAC[]
        , PROVE_TAC[VALID_def, IMP_def]
          THEN UNDISCH_TAC(--`∀q. HOARE gcl (wlp gcl q) q`--)
          THEN FIRST_X_ASSUM (MP_TAC)
          THEN REWRITE_TAC[lemma]
          THEN ASSUME_TAC(GEN_ALL(HOARE_precond_strengthening_thm))
          THEN PROVE_TAC[]
        ]
      , PROVE_TAC[HOARE_loop_thm1]
      ]

    ]
  ) ;



val reduce_thm = prove
   (--`VALID (IMP p (wlp stmt q)) ==> HOARE stmt p q`--,
    STRIP_TAC
    THEN MATCH_MP_TAC (GEN_ALL HOARE_precond_strengthening_thm)
    THEN EXISTS_TAC (--`wlp stmt q`--)
    THEN ASM_REWRITE_TAC []
    THEN REWRITE_TAC [SOUND_wlp_thm]
   ) ;

val example1 = --`
    SEQS [
       ASSUME (\s. s "x" > s "y") ;
       ASG "x" (\s. s "x" + 1) ;
       ASG "y" (\s. s "y" + 1)
    ]
    `-- ;

val example1_valid_thm = prove
   (--`HOARE ^example1 TT (\s. s "x" > s "y")`--,
    MATCH_MP_TAC reduce_thm
    THEN REWRITE_TAC [VALID_def, IMP_def]
    THEN BETA_TAC
    THEN REWRITE_TAC [TT_def, SEQS_def]
    THEN STRIP_TAC
    THEN REWRITE_TAC [wlp_def]
    THEN BETA_TAC
    THEN BETA_TAC
    THEN CONV_TAC (DEPTH_CONV string_EQ_CONV)
    THEN REWRITE_TAC []
    THEN COOPER_TAC
);


val example2 = --` SEQS
 [ ASSUME (λs. ¬ (s "x" = s "y"))
 ; (IFTHENELSE (λs. s "y" > s "x")
    (ASG "y" (λs. s "y" - s "x"))
    (ASG "x" (λs. s "x" - s "y")))
 ]
 `-- ;

val example2_thm = prove
  (--`HOARE ^example2 (\s. s "x" > 0 /\ s "y" > 0) (\s. s "x" + s "y" > 0)`--,
    MATCH_MP_TAC reduce_thm
    THEN REWRITE_TAC [VALID_def, IMP_def]
    THEN BETA_TAC
    THEN REWRITE_TAC [SEQS_def]
    THEN STRIP_TAC
    THEN REWRITE_TAC [wlp_def]
    THEN BETA_TAC
    THEN DISCH_TAC
    THEN DISCH_TAC
    THEN CONJ_TAC
    THENL [
      DISCH_TAC
      THEN BETA_TAC
      THEN (CONV_TAC (DEPTH_CONV string_EQ_CONV))
      THEN REWRITE_TAC []
      THEN COOPER_TAC,
      DISCH_TAC
      THEN BETA_TAC
      THEN (CONV_TAC (DEPTH_CONV string_EQ_CONV))
      THEN REWRITE_TAC []
      THEN COOPER_TAC
    ]

  );



