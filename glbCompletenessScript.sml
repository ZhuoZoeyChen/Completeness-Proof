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
 TODO
  10 Sep 

  DONE 1. Change CPLAxioms to use ptaut; (ptaut includes all the propositional axioms)
  {might use Logics of Time and Computation. R. I. Goldblatt CSLI Lecture Notes Number 7,
Center for the Study of Language and Information, Stanford, 1987}

  DONE 2. use subst instead of set comprehension (?) (use atomic formulae in the set)
*)

Definition CPLAxioms_def:
CPLAxioms = {a | ptaut a}
End

Definition KAxioms_def:
  KAxioms = 
      CPLAxioms 
    ∪
      {(□ (VAR 0 -> VAR 1)) -> ((□ (VAR 0)) -> (□ (VAR 1)))}
End

Inductive gtt:
	(∀f. f ∈ G ⇒ gtt Ax G f) ∧
	(∀f s. f ∈ Ax ⇒ gtt Ax G (subst s f)) ∧ 
	(∀f1 f2. gtt Ax G f1 ∧ gtt Ax G (f1 -> f2) ⇒ gtt Ax G f2) ∧
	(∀f. gtt Ax G f ⇒ gtt Ax G (□ f))
End

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


(*  NOT NOT A = A 
    A OR NOT A = T
    AND elimination 
    A <-> A
    A -> A OR B
    A <-> NOT NOT A
    A -> (B -> (A AND B))
*)
Theorem ptaut_thms[simp]:
  ptaut (¬¬(VAR 0) -> (VAR 0)) ∧ ptaut ((VAR 0) -> ¬¬(VAR 0)) ∧
  ptaut (DISJ (¬VAR 0) (VAR 0)) ∧ ptaut (DISJ (VAR 0) (¬VAR 0)) ∧
  ptaut ((AND (VAR 0) (VAR 1)) -> (VAR 0)) ∧ ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 1)) ∧
  ptaut (DOUBLE_IMP (VAR 0) (VAR 0)) ∧
  ptaut ((VAR 0) -> (DISJ (VAR 0) (VAR 1))) ∧
  ptaut (DOUBLE_IMP (VAR 0) ¬¬(VAR 0)) ∧
  ptaut (DOUBLE_IMP (AND (VAR 0) (VAR 1)) (AND (VAR 1) (VAR 0))) ∧
  ptaut ((VAR 0) -> ((VAR 1) -> (AND (VAR 1) (VAR 0))))  ∧
  ptaut (DOUBLE_IMP ⊥ ⊥) ∧
  ptaut (IMP (DOUBLE_IMP (VAR 0) (VAR 1)) (DOUBLE_IMP (NOT (VAR 0)) (NOT (VAR 1))))
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
∀Q P G.  ptaut (Q: num form)  ∧ (∃f. subst f Q = P) ==> gtt KAxioms G P
Proof 
  rw[] >>
  `Q ∈ {a | ptaut a} ∪ {□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1)}` by simp[UNION_DEF] >>
  metis_tac[gtt_rules, KAxioms_def, CPLAxioms_def]
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
  rw[] >>
  `gtt KAxioms G (A -> (DISJ A B))` by metis_tac[subst_ptaut] >>
   metis_tac[gtt_rules]
QED 


Theorem gttDoubleImp:
  gtt KAxioms G (DOUBLE_IMP A B) ⇒ (gtt KAxioms G A ⇔ gtt KAxioms G B)
Proof 
  rw[DOUBLE_IMP_def] >> rw[EQ_IMP_THM] >> fs[]
  >- (`gtt KAxioms G (A -> B)` by metis_tac[gtt_conj1] >> metis_tac[gtt_rules])
  >> `gtt KAxioms G (B -> A)` by metis_tac[gtt_conj2] >> metis_tac[gtt_rules]
QED



(* gtt Ax ∅ P ==> gtt Ax ∅ (subst s P)*)
(*
Theorem gtt_empty_subst:
  gtt (Ax: num form -> bool) ∅ (P:num form) ⇒ gtt Ax ∅ (subst (s:num -> num form) P) 
Proof 
  rw[] >> `(subst s P) ∈ ∅ ∨ (∃f s. (subst s P) = subst s f ∧ f ∈ Ax) ∨
            (∃(f1: num form). gtt Ax G f1 ∧ gtt Ax ∅ (f1 -> (subst s P))) ∨
            ∃(f: num form). (subst s P) = □ f ∧ gtt Ax ∅ f` suffices_by simp[gtt_cases]
  Cases_on `Ax = ∅` >> rw[] >- (Cases_on `gtt_cases`)rw[gtt_rules] >>  
QED
*)

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


(* gtt Ax ∅ ((A->B) -> (DIAM A -> DIAM B))*)
(*
Theorem gtt_add_DIAM:
 ∀A B. gtt Ax ∅ ((A->B) -> (DIAM A -> DIAM B))
Proof 
  `subst (λs. DIAM (VAR s)) ((VAR 0) -> (VAR 1)) = (DIAM (VAR 0) -> DIAM (VAR 1))` by simp[subst_def] >>

  metis_tac[subst_ptaut]
QED 
*)

Theorem gtt_double_imp:
 ∀A. gtt KAxioms ∅ (DOUBLE_IMP A A) 
Proof 
  `ptaut (DOUBLE_IMP (VAR 0) (VAR 0))` by simp[ptaut_thms] >>
  `∀A. subst (λs. A) (DOUBLE_IMP (VAR 0) (VAR 0)) = (DOUBLE_IMP A A)`
     by simp[DOUBLE_IMP_def, subst_def, AND_def] >>
   metis_tac[subst_ptaut]
QED 


Theorem gtt_disj_double_imp:
∀XA XB YA YB. 
  gtt KAxioms ∅ (DOUBLE_IMP XA XB) ∧ gtt KAxioms ∅ (DOUBLE_IMP YA YB) 
⇒ gtt KAxioms ∅ (DOUBLE_IMP (DISJ XA YA) (DISJ XB YB))
Proof 
  rw[] 
QED 

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

Theorem gtt_subst_eqv_terms:
∀X A B. 
    gtt KAxioms ∅ (DOUBLE_IMP A B)
  ==> 
    gtt KAxioms ∅ (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X))
Proof 
  rw[] >>
  Induct_on`X` >> rw[]
  >- (rename [`gtt KAxioms ∅ (DOUBLE_IMP (DISJ (subst (λv. A) X) (subst (λv. A) Y))
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
  >- (`ptaut (DOUBLE_IMP ⊥ ⊥)` by simp[] >>
      irule subst_ptaut >> qexists_tac `DOUBLE_IMP ⊥ ⊥` >> rw[] >> qexists_tac`λs. A`
      >> metis_tac[subst_def, DOUBLE_IMP_def, AND_def, IMP_def, subst_ptaut])
  >- (`ptaut (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (¬VAR 0) (¬VAR 1))` by simp[] 
      >> `subst (λs. if s = 0 then (subst (λv. A) X) else (subst (λv. B) X)) 
           (DOUBLE_IMP (VAR 0) (VAR 1) -> DOUBLE_IMP (¬VAR 0) (¬VAR 1))
             = (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) -> DOUBLE_IMP (¬(subst (λv. A) X)) (¬(subst (λv. B) X)))`
            by simp[DOUBLE_IMP_def, AND_def, IMP_def, subst_def]
      >> `gtt KAxioms ∅ (DOUBLE_IMP (subst (λv. A) X) (subst (λv. B) X) ->
         DOUBLE_IMP (¬subst (λv. A) X) (¬subst (λv. B) X))` by metis_tac[subst_ptaut]
      >> metis_tac[gtt_rules]
      )
  >> 
  >> rw[DOUBLE_IMP_def] >> rw[IMP_def]
QED


Theorem gTk:
 ∀(p :num form list). (KGproof Ax p) ⇒ (∀f. (MEM f p) ⇒ gtt (Ax ∪ KAxioms) ∅ f)
Proof
  Induct_on `KGproof` >> rw[] >> simp[gtt_rules, gttEmpG]
  >- metis_tac[gtt_rules]  (* MP *)
  >- (`subst (λs. if s = 0 then form1 else form2)
        (□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1))
        = (□ (form1 -> form2) -> □ form1 -> □ form2) ` by simp[] >>
        `(□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1)) ∈ (Ax ∪ KAxioms)` by simp[KAxioms_def] >>
      metis_tac[gtt_rules])  (* K axiom instance *)
(* DIAM q -> NOT BOX (NOT q) *)
  >- ((*rw[BOX_def] >> `subst (λs. form) ((VAR 0) -> ¬¬ (VAR 0)) = (form -> ¬¬ form)` by simp[ptaut_thms] >>
     `ptaut ((VAR 0) -> ¬¬ (VAR 0))` by simp[ptaut_thms] >> 
     `gtt KAxioms ∅ (form -> ¬¬form)` by metis_tac[subst_ptaut] >>
     `gtt (Ax ∪ KAxioms) ∅ (form -> ¬¬form)` by metis_tac[gtt_Ext, UNION_COMM] >>
     rw[gtt_rules, KAxioms_def, CPLAxioms_def] >> 
      rw[IMP_def] 
      >> rw[ptaut_def]*)
      rw[] >> cheat)
(* NOT BOX (NOT q) -> DIAM q *)
  >- cheat
  >- metis_tac[subst_ptaut, gtt_Ext, UNION_COMM, subst_self] (* ptaut f *)
  >> metis_tac[gtt_Ext, UNION_COMM, subst_self, gtt_rules]
QED


Theorem kTg:
  (∀f ∈ p. gtt (Ax ∪ KAxioms) ∅ f) ⇒ ∀Ax p. KGproof Ax p
Proof 

QED

val _ = export_theory()
