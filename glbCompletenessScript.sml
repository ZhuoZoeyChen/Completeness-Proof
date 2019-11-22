open HolKernel Parse boolLib bossLib;
open nlistTheory listTheory;
open pred_setTheory;
open chap1Theory;

val _ = new_theory "glbCompleteness";

(*
val (KGproof_rules, KGproof_ind, KGproof_cases) = Hol_reln`
  KGproof (Ax:'a form set) [] /\
  (!p form1 form2.
    KGproof Ax p /\ MEM (IMP form1 form2) p /\ MEM form1 p ==>
    KGproof Ax (p ++ [form2])) /\
  (!p form f.
    KGproof Ax p /\ MEM form p ==> KGproof Ax (p ++ [subst f form])) /\
  (!p form. KGproof Ax p /\ MEM form p ==> KGproof Ax (p ++ [BOX form])) /\
  (!p form1 form2. KGproof Ax p ==> KGproof Ax (p ++ [IMP (BOX (IMP form1 form2)) (IMP (BOX form1) (BOX form2))])) /\
  (!p form. KGproof Ax p ==> KGproof Ax (p ++ [IMP (DIAM form) (NOT (BOX (NOT form)))])) /\
  (!p form. KGproof Ax p ==> KGproof Ax (p ++ [IMP (NOT (BOX (NOT form))) (DIAM form)])) /\
  (!p form. KGproof Ax p /\ ptaut form ==> KGproof Ax (p ++ [form])) /\
  (!p form. KGproof Ax p /\ form IN Ax ==> KGproof Ax (p ++ [form]))
`;    
*)
 
(*

  {might use Logics of Time and Computation. R. I. Goldblatt CSLI Lecture Notes Number 7,
Center for the Study of Language and Information, Stanford, 1987}

*)

(* gtt: global turnstile t? *)

Definition CPLAxioms_def:
CPLAxioms = {a | ptaut a}
End

Definition KAxioms_def:
  KAxioms = 
      CPLAxioms 
    ∪
      {(□ (VAR 0 -> VAR 1)) -> ((□ (VAR 0)) -> (□ (VAR 1)))}
End

Definition KDAxioms_def:
  KDAxioms = 
      CPLAxioms 
    ∪
      {(□ (VAR 0 -> VAR 1)) -> ((□ (VAR 0)) -> (□ (VAR 1)))}
    ∪ 
      {DOUBLE_IMP (◇ (VAR 0)) (¬□ (¬VAR 0))}
End

Inductive gtt:
	(∀f. f ∈ G ⇒ gtt Ax G f) ∧
	(∀f s. f ∈ Ax ⇒ gtt Ax G (subst s f)) ∧ 
	(∀f1 f2. gtt Ax G f1 ∧ gtt Ax G (f1 -> f2) ⇒ gtt Ax G f2) ∧
	(∀f. gtt Ax G f ⇒ gtt Ax G (□ f))
End

(*
--------------------------------------------
------ Equivalence between gtt and kG ------
--------------------------------------------
*)

Theorem subst_compose:
  ∀f g x. subst g (subst f x) = subst ((subst g) o f) x 
Proof
  Induct_on `x` >> rw[subst_def]
QED

Theorem subst_self:
  ∀f. f = subst (λi. VAR i) f 
Proof 
  Induct_on `f` >> simp[subst_def]
QED

Theorem subst_BOX[simp]:
  subst f (BOX form) = BOX (subst f form)
Proof 
  rw[BOX_def]
QED

Theorem subst_IMP[simp]:
  subst f (IMP form1 form2) = IMP (subst f form1) (subst f form2)
Proof 
  rw[IMP_def]
QED 

Theorem gttSubst:
 ∀s f. gtt Ax G f ⇒ gtt Ax {subst s g | g ∈ G} (subst s f)
Proof 
  Induct_on `gtt` >> 
  rw[gtt_rules, subst_def] 
    >- (`(subst s f) ∈ {subst s g| g ∈ G}` suffices_by rw[gtt_rules] 
          >> fs[] >> metis_tac[])
    >- (rw[subst_compose] >> rw[gtt_rules])
    >> `!s. (subst s (f -> f')) = ((subst s f) -> (subst s f'))` 
          by metis_tac[subst_def,IMP_def] 
          >> metis_tac[gtt_rules]
QED

Theorem gttEmpG:
  ∀s f. gtt Ax ∅ f ⇒ gtt Ax ∅ (subst s f)
Proof
  Induct_on `gtt` >> 
  rw[gtt_rules, subst_def] 
    >- (rw[subst_compose] >> rw[gtt_rules])
    >> `!s. (subst s (f -> f')) = ((subst s f) -> (subst s f'))` 
          by metis_tac[subst_def,IMP_def] 
          >> metis_tac[gtt_rules]
QED

Theorem gttAx:
  ∀f s. f ∈ Ax ⇒ gtt Ax G f 
Proof
  rw[] >> `∀s. gtt Ax G (subst s f)` by rw[gtt_rules]
  >>  `f = subst (λi. VAR i) f` by rw[subst_self] 
  >> `gtt Ax G f` by metis_tac[]
QED

Theorem gttK:
  ∀form1 form2. gtt KAxioms G (subst (λs. if s=0 then form1 else form2) (□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1)))
Proof 
  rw[subst_def, gtt_rules, KAxioms_def]
QED


(*  
    
    NOT NOT A = A 
    A OR NOT A = T
    AND elimination 
    A <-> A
    A -> A OR B
    A <-> NOT NOT A

*)
Theorem ptaut_thms[simp]:
  ptaut (¬¬(VAR 0) -> (VAR 0)) ∧ ptaut ((VAR 0) -> ¬¬(VAR 0)) ∧
  ptaut (DISJ (¬VAR 0) (VAR 0)) ∧ ptaut (DISJ (VAR 0) (¬VAR 0)) ∧
  ptaut ((AND (VAR 0) (VAR 1)) -> (VAR 0)) ∧ ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 1)) ∧
  ptaut (DOUBLE_IMP (VAR 0) (VAR 0)) ∧
  ptaut ((VAR 0) -> (DISJ (VAR 0) (VAR 1))) ∧
  ptaut (DOUBLE_IMP (VAR 0) ¬¬(VAR 0)) ∧
  ptaut (DOUBLE_IMP (AND (VAR 0) (VAR 1)) (AND (VAR 1) (VAR 0))) ∧
   (*  A -> (B -> (A AND B)) *)
  ptaut ((VAR 0) -> ((VAR 1) -> (AND (VAR 0) (VAR 1))))  ∧
  (*  A -> (B -> (B AND A)) *)
  ptaut ((VAR 0) -> ((VAR 1) -> (AND (VAR 1) (VAR 0)))) ∧
  ptaut (DOUBLE_IMP ⊥ ⊥) ∧
  ptaut (IMP (DOUBLE_IMP (VAR 0) (VAR 1)) (DOUBLE_IMP (NOT (VAR 0)) (NOT (VAR 1)))) ∧
  ptaut ((DOUBLE_IMP (VAR 0) (VAR 1)) -> (IMP (VAR 0) (VAR 1))) ∧
  ptaut ((DOUBLE_IMP (VAR 0) (VAR 1)) -> (IMP (VAR 1) (VAR 0)))
Proof 
  simp[ptaut_def, AND_def, IMP_def, DOUBLE_IMP_def] >>
  metis_tac[]
QED

Theorem ptaut_disj_double_imp[simp]:
  ptaut (IMP (DOUBLE_IMP (VAR 0) (VAR 1)) (IMP (DOUBLE_IMP (VAR 2) (VAR 3)) ( DOUBLE_IMP (DISJ (VAR 0) (VAR 2)) (DISJ (VAR 1) (VAR 3))) ) )
Proof
  simp[ptaut_def, AND_def, IMP_def, DOUBLE_IMP_def] >>
  metis_tac[]
QED 

(* All instances of Axims are gtt provable *)
Theorem subst_ptaut[simp]:
∀Q P G Ax. ptaut (Q: num form)  ∧ (∃f. subst f Q = P) ==> gtt (Ax ∪ KDAxioms) G P
Proof 
  rw[] >>
  `Q ∈ Ax ∪ KDAxioms` by rw[UNION_DEF, KDAxioms_def, CPLAxioms_def] >>
  metis_tac[gtt_rules]
QED 

Theorem gtt_Ext:
  gtt Ax G f ⇒ gtt (Ax ∪ Ext) G f
Proof
  Induct_on `gtt` >> rw[gtt_rules] >> metis_tac[gtt_rules]
QED

Theorem gtt_conj1:
  gtt KAxioms G (AND A B) ⇒ gtt KAxioms G A
Proof 
  `ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 0))` by rw[ptaut_thms] >>
  `(IMP (AND (VAR 0) (VAR 1)) (VAR 0)) ∈ {a | ptaut a}` by simp[] >>
  `subst (λs. if s = 0 then A else B) (IMP (AND (VAR 0) (VAR 1)) (VAR 0)) = (IMP (AND A B) A)` 
    by simp[subst_def, AND_def, IMP_def] >>
  rw[] >> `gtt KAxioms G (subst (λs. if s = 0 then A else B) (AND (VAR 0) (VAR 1) -> VAR 0))` 
   by simp[gtt_rules, KAxioms_def, CPLAxioms_def] >>
  `gtt KAxioms G (IMP (AND A B) A)` by rfs[] >>
  metis_tac[gtt_rules]
QED 

Theorem gtt_conj2:
  gtt KAxioms G (AND A B) ⇒ gtt KAxioms G B
Proof 
  `ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 1))` by rw[ptaut_thms] >>
  `(IMP (AND (VAR 0) (VAR 1)) (VAR 1)) ∈ {a | ptaut a}` by simp[] >>
  `subst (λs. if s = 0 then A else B) (IMP (AND (VAR 0) (VAR 1)) (VAR 1)) = (IMP (AND A B) B)` 
    by simp[subst_def, AND_def, IMP_def] >>
  rw[] >> `gtt KAxioms G (subst (λs. if s = 0 then A else B) (AND (VAR 0) (VAR 1) -> VAR 1))` 
   by simp[gtt_rules, KAxioms_def, CPLAxioms_def] >>
  `gtt KAxioms G (IMP (AND A B) B)` by rfs[] >>
  metis_tac[gtt_rules]
QED 

Theorem gtt_disj:
  gtt KAxioms G A ⇒ gtt KAxioms G (DISJ A B)
Proof 
  `subst (λs. if s = 0 then A else B) ((VAR 0) -> (DISJ (VAR 0) (VAR 1))) = (A -> (DISJ A B))` by simp[subst_def] >>
  `ptaut ((VAR 0) -> (DISJ (VAR 0) (VAR 1)))` by rw[ptaut_thms] >>
  `gtt Ax G (DOUBLE_IMP A B -> A -> B)` by metis_tac[subst_ptaut] >>

   metis_tac[gtt_rules]
QED 


Theorem gtt_Double_Imp:
  gtt KAxioms G (DOUBLE_IMP A B) ⇒ (gtt KAxioms G A ⇔ gtt KAxioms G B)
Proof 
  rw[DOUBLE_IMP_def] >> rw[EQ_IMP_THM] >> fs[]
  >- (`gtt KAxioms G (A -> B)` by metis_tac[gtt_conj1] >> metis_tac[gtt_rules])
  >> `gtt KAxioms G (B -> A)` by metis_tac[gtt_conj2] >> metis_tac[gtt_rules]
QED



(* gtt Ax ∅ P ==> gtt Ax ∅ (subst s P)*)

Theorem gtt_empty_subst:
∀P.  gtt (Ax: num form -> bool) ∅ (P:num form) ⇒ gtt Ax ∅ (subst (s:num -> num form) P) 
Proof 
  Induct_on`gtt`>> rw[] 
  >- (rw[subst_compose] >> metis_tac[gtt_rules])
  >- metis_tac[gtt_rules]
  >> metis_tac[gtt_rules] 
QED


Theorem gtt_not_not:
  ∀A. gtt KAxioms G (A -> ¬¬A) ∧ gtt KAxioms G (¬¬A -> A)
Proof 
  `ptaut (¬¬(VAR 0) -> (VAR 0))  ∧ ptaut ((VAR 0) -> ¬¬(VAR 0))` by simp[ptaut_thms] >>
  rw[]
  >- (`subst (λs. A) ((VAR 0) -> ¬¬(VAR 0)) = (A -> ¬¬A)` 
    by simp[subst_def] >> metis_tac[subst_ptaut])
  >>  `subst (λs. A) (¬¬(VAR 0) -> (VAR 0)) = (¬¬A -> A)` 
    by simp[subst_def] >> metis_tac[subst_ptaut]
QED 

Theorem gtt_not_not_double:
  ∀A. gtt KAxioms G (DOUBLE_IMP A ¬¬A)
Proof 
  `ptaut (DOUBLE_IMP (VAR 0) (¬¬VAR 0))` by simp[ptaut_thms] >>
  `∀A. subst (λs. A) (DOUBLE_IMP (VAR 0) (¬¬VAR 0)) = (DOUBLE_IMP A ¬¬A)`
     by simp[DOUBLE_IMP_def, subst_def, AND_def] >>
   metis_tac[subst_ptaut]
QED 

(*
Theorem gtt_diam_not_not:
∀G A.  gtt KAxioms G (DIAM (¬¬ A)) ⇔ gtt KAxioms G (DIAM A)
Proof 
  rw[EQ_IMP_THM] 
  >- 
  >>
  Induct_on`gtt` >> rw[]
QED 
*)
(*
Theorem gtt_A_not_not_B:
  ∀A B. gtt KAxioms G (A -> B) ⇒ gtt KAxioms G (A -> ¬¬B)
Proof 
  Induct_on`gtt` >> rw[]
  >- (fs[IMP_def] >> )
  >-
  >-
  >>
QED 
*)

(* gtt Ax ∅ ((A->B) -> (DIAM A -> DIAM B))*)

(*
Theorem gtt_add_DIAM:
 ∀A B. gtt Ax ∅ (A -> B) ⇒ gtt Ax ∅ (DIAM A -> DIAM B)
Proof 
  Induct_on`gtt` >> rw[]
  >- 
  >-
  >>

  `subst (λs. DIAM (VAR s)) ((VAR 0) -> (VAR 1)) = (DIAM (VAR 0) -> DIAM (VAR 1))` by simp[subst_def] >>

  metis_tac[subst_ptaut]
QED 

*)

Theorem gtt_double_imp_self:
 ∀A. gtt KAxioms ∅ (DOUBLE_IMP A A) 
Proof 
  `ptaut (DOUBLE_IMP (VAR 0) (VAR 0))` by simp[ptaut_thms] >>
  `∀A. subst (λs. A) (DOUBLE_IMP (VAR 0) (VAR 0)) = (DOUBLE_IMP A A)`
     by simp[DOUBLE_IMP_def, subst_def, AND_def] >>
   metis_tac[subst_ptaut]
QED 

(*
Theorem gtt_disj_double_imp:
∀XA XB YA YB. 
  gtt KAxioms ∅ (DOUBLE_IMP XA XB) ∧ gtt KAxioms ∅ (DOUBLE_IMP YA YB) 
⇒ gtt KAxioms ∅ (DOUBLE_IMP (DISJ XA YA) (DISJ XB YB))
Proof 
  cheat
QED 
*)

(*
Theorem gtt_ptaut[simp]:
  ∀fml G. ptaut fml ⇒ gtt KAxioms G fml
Proof 
  rw[] >> `fml = subst (λi. VAR i) fml` by rw[subst_self]
  >> irule subst_ptaut
  >> qexists_tac`fml` >> rw[]
  >- 
  >> 
QED 
*)
(*
Theorem gtt_transitive_double_imp:
∀G A B C.  gtt KAxioms G (DOUBLE_IMP A B) ∧ gtt KAxioms G (DOUBLE_IMP B C)
          ==> 
           gtt KAxioms G (DOUBLE_IMP A C)
Proof 

QED
*)

(*

Theorem gtt_subst_eqv_terms:
∀X A B. 
    gtt KAxioms ∅ (DOUBLE_IMP A B)
  ==> 
    gtt KAxioms ∅ (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X))
Proof 
  Induct_on`X` 
  >- rw[]
  >- (rw[] >> rename [`gtt KAxioms ∅ (DOUBLE_IMP (DISJ (subst (λv. A) X) (subst (λv. A) Y))
             (DISJ (subst (λv. B) X) (subst (λv. B) Y)))`] 
      >> `ptaut (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (VAR 2) (VAR 3) ->
       DOUBLE_IMP (DISJ (VAR 0) (VAR 2)) (DISJ (VAR 1) (VAR 3)))` by rw[ptaut_disj_double_imp]
      >> `subst (λs. case s of 
                       | 0 => subst (λv. A) X
                       | 1 => subst (λv. B) X
                       | 2 => subst (λv. A) Y
                       | 3 => subst (λv. B) Y
                  ) (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (VAR 2) (VAR 3) ->
       DOUBLE_IMP (DISJ (VAR 0) (VAR 2)) (DISJ (VAR 1) (VAR 3))) =
        (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) -> DOUBLE_IMP (subst (λv. A) Y) (subst (λv. B) Y) ->
       DOUBLE_IMP (DISJ (subst (λv. A) X) (subst (λv. A) Y)) (DISJ (subst (λv. B) X) (subst (λv. B) Y)))`  
       by simp[DOUBLE_IMP_def, subst_def, AND_def, IMP_def] 
       >> `gtt KAxioms ∅ (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) ->
         DOUBLE_IMP (subst (λv. A) Y) (subst (λv. B) Y) ->
         DOUBLE_IMP (DISJ (subst (λv. A) X) (subst (λv. A) Y))
           (DISJ (subst (λv. B) X) (subst (λv. B) Y)))` by metis_tac[subst_ptaut]
       >> metis_tac[gtt_rules])
  >- (rw[] >> `ptaut (DOUBLE_IMP ⊥ ⊥)` by simp[] >>
      irule subst_ptaut >> qexists_tac `DOUBLE_IMP ⊥ ⊥` >> rw[] >> qexists_tac`λs. A`
      >> metis_tac[subst_def, DOUBLE_IMP_def, AND_def, IMP_def, subst_ptaut])
  >- (rw[] >> `ptaut (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (¬VAR 0) (¬VAR 1))` by simp[] 
      >> `subst (λs. if s = 0 then (subst (λv. A) X) else (subst (λv. B) X)) 
           (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (¬VAR 0) (¬VAR 1))
             = (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) -> DOUBLE_IMP (¬(subst (λv. A) X)) (¬(subst (λv. B) X)))`
            by simp[DOUBLE_IMP_def, AND_def, IMP_def, subst_def]
      >> `gtt KAxioms ∅ (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) ->
         DOUBLE_IMP (¬subst (λv. A) X) (¬subst (λv. B) X))` by metis_tac[subst_ptaut]
      >> metis_tac[gtt_rules])
  >> rw[]
  >> 
  >> metis_tac[gtt_empty_subst]
  >> rw[DOUBLE_IMP_def] >> rw[IMP_def]
QED
*)

Theorem gtt_double_imp_decompose_ltr:
∀A B Ax G. (KDAxioms ⊆ Ax) ⇒ gtt Ax G (DOUBLE_IMP A B) ⇒ gtt Ax G (A -> B)
Proof 
  rw[] >> 
  `subst (λs. if s = 0 then A else B) (DOUBLE_IMP (VAR 0) (VAR 1) -> VAR 0 -> VAR 1) = (DOUBLE_IMP A B -> A -> B)`
    by simp[DOUBLE_IMP_def, subst_def, IMP_def, AND_def] >>
  `ptaut (DOUBLE_IMP (VAR 0) (VAR 1) -> VAR 0 -> VAR 1)` by simp[ptaut_thms] >>
  `gtt (Ax ∪ KDAxioms) G (DOUBLE_IMP A B -> A -> B)` by metis_tac[subst_ptaut] >> 
  `gtt Ax G (DOUBLE_IMP A B -> A -> B)` by metis_tac[SUBSET_UNION_ABSORPTION, UNION_COMM] >>
  metis_tac[gtt_rules]
QED 

Theorem gtt_double_imp_decompose_rtl:
∀A B Ax G. (KDAxioms ⊆ Ax) ⇒ gtt Ax G (DOUBLE_IMP A B) ⇒ gtt Ax G (B -> A)
Proof 
  rw[] >> 
  `subst (λs. if s = 0 then A else B) (DOUBLE_IMP (VAR 0) (VAR 1) -> VAR 1 -> VAR 0) = (DOUBLE_IMP A B -> B -> A)`
    by simp[DOUBLE_IMP_def, subst_def, IMP_def, AND_def] >>
  `ptaut (DOUBLE_IMP (VAR 0) (VAR 1) -> VAR 1 -> VAR 0)` by simp[ptaut_thms] >>
  `gtt (Ax ∪ KDAxioms) G (DOUBLE_IMP A B -> B -> A)` by metis_tac[subst_ptaut] >> 
  `gtt Ax G (DOUBLE_IMP A B -> B -> A)` by metis_tac[SUBSET_UNION_ABSORPTION, UNION_COMM] >>
  metis_tac[gtt_rules]
QED 


Theorem gTk:
 ∀(p :num form list). (KGproof Ax p) ⇒ (∀f. (MEM f p) ⇒ gtt (Ax ∪ KDAxioms) ∅ f)
Proof
  Induct_on `KGproof` >> rw[] >> simp[gtt_rules, gttEmpG]
  >- metis_tac[gtt_rules]  (* MP *)
  >- (`subst (λs. if s = 0 then form1 else form2)
        (□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1))
        = (□ (form1 -> form2) -> □ form1 -> □ form2) ` by simp[] >>
        `(□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1)) ∈ (Ax ∪ KDAxioms)` by simp[KDAxioms_def] >>
      metis_tac[gtt_rules])  (* K axiom instance *)
(* DIAM q -> NOT BOX (NOT q) *)
  >- (`subst (λs. form) (DOUBLE_IMP (◇ (VAR 0)) (¬□ (¬VAR 0))) = (DOUBLE_IMP (◇ form) (¬□ (¬form)))`
         by simp[DOUBLE_IMP_def, IMP_def, BOX_def, subst_def, AND_def] >> 
      `(DOUBLE_IMP (◇ (VAR 0)) (¬□ (¬VAR 0))) ∈ (Ax ∪ KDAxioms)` 
          by simp[KDAxioms_def] >> 
      `gtt (Ax ∪ KDAxioms) ∅ (DOUBLE_IMP (◇ form) (¬□ (¬form)))` by metis_tac[gtt_rules] >>
       irule gtt_double_imp_decompose_ltr >>
       rw[])
(* NOT BOX (NOT q) -> DIAM q *)
  >- (`subst (λs. form) (DOUBLE_IMP (◇ (VAR 0)) (¬□ (¬VAR 0))) = (DOUBLE_IMP (◇ form) (¬□ (¬form)))`
         by simp[DOUBLE_IMP_def, IMP_def, BOX_def, subst_def, AND_def] >> 
      `(DOUBLE_IMP (◇ (VAR 0)) (¬□ (¬VAR 0))) ∈ (Ax ∪ KDAxioms)` 
          by simp[KDAxioms_def] >> 
      `gtt (Ax ∪ KDAxioms) ∅ (DOUBLE_IMP (◇ form) (¬□ (¬form)))` by metis_tac[gtt_rules] >>
       irule gtt_double_imp_decompose_rtl >>
       rw[])
  >- metis_tac[subst_ptaut, gtt_Ext, UNION_COMM, subst_self] (* ptaut f *)
  >> metis_tac[gtt_Ext, UNION_COMM, subst_self, gtt_rules]
QED


Theorem kTg:
  ∀Ax (f: num form). gtt (Ax ∪ KDAxioms) ∅ f ⇒ ∃ (p:num form list). MEM f p ∧ KGproof Ax p 
Proof
  strip_tac >>
  `KGproof Ax []` by metis_tac[KGproof_rules] >>
  Induct_on `gtt` >> rw[]
  >- (qexists_tac `[f; subst s f]` >> rw[] >>
      `KGproof Ax [f]` by metis_tac[KGproof_rules, APPEND] >>
      metis_tac[KGproof_rules, APPEND, MEM])
  >- (fs[KDAxioms_def, CPLAxioms_def] 
      >- (qexists_tac `[f; subst s f]` >> rw[] >>
      `KGproof Ax [f]` by metis_tac[KGproof_rules, APPEND] >>
      metis_tac[KGproof_rules, APPEND, MEM])
      >- (qexists_tac `[□ (s 0 -> s 1) -> □ (s 0) -> □ (s 1)]` >> rw[] 
           >> metis_tac[KGproof_rules, APPEND, MEM])
      >> rw[DOUBLE_IMP_def]
      >> qabbrev_tac `A = IMP (DIAM (VAR 0)) (NOT (BOX (NOT (VAR 0))))`
      >> qabbrev_tac `B = IMP (NOT (BOX (NOT (VAR 0)))) (DIAM (VAR 0))`
      >> qexists_tac `[A; B;((VAR 0) -> ((VAR 1) -> (AND (VAR 0) (VAR 1))));
             A -> (B -> (AND A B)); B -> (AND A B); AND A B; subst s (AND A B)]` 
      >> rw[]
      >> `subst (λs. if s = 0 then A else B) ( (VAR 0) -> ( (VAR 1) -> ( AND (VAR 0) (VAR 1) ) ) ) 
        = (A -> (B -> (AND A B)))` by simp[subst_def, IMP_def, AND_def]
      >> `KGproof Ax
          [A; B; VAR 0 -> VAR 1 -> AND (VAR 0) (VAR 1);
           subst (λs. if s = 0 then A else B) ( (VAR 0) -> ( (VAR 1) -> ( AND (VAR 0) (VAR 1) ) ) )]`
              by metis_tac[KGproof_rules, APPEND, ptaut_thms, MEM] 
      >> rfs[]
      >> metis_tac[KGproof_rules, APPEND, MEM])
  >- (qexists_tac`p'++p++[f']` >> rw[] >>
      `KGproof Ax (p'++p)` by metis_tac[KGproof_APPEND] >>
      metis_tac[KGproof_rules, APPEND, MEM, KGproof_APPEND, MEM_APPEND])
  >> qexists_tac`p++[□ f]` >> rw[] >> metis_tac[KGproof_rules, APPEND, MEM, KGproof_APPEND, MEM_APPEND]
QED 



(*
--------------------------------------------------------
-------------- Global Completeness Proof  --------------
--------------------------------------------------------
*)

(* Consistent Definition *)
(*
Theorem Consist_Set:
  Consist_Set S = ∀x. x ∈ S ⇒ (NOT x) ∉ S
Proof 
QED

Theorem Inconsist_Set:
Proof 
QED 
*)

(* Lemma 6: Every consistent set Y is extendable into a max-consist X where Y is a proper subset of X *)
(*
Theorem MCS_Constrct:
   
Proof 
QED 
*)
(* Lemma 
*)



(*
Theorem gtt_Completenss:

Proof 
QED 
*)

val _ = export_theory()
