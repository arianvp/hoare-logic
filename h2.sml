use "h1.sml";

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
       ASG "y" (\s. s "y" + 1) ;
       ASSERT (\s. s "x" > s "y")
    ]
    `-- ;

val example1_valid_thm = prove
   (--`HOARE ^example1 TT TT`--,
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
