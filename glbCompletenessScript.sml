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

Theorem subst_self:
  ∀f. f = subst (λi. VAR i) f 
Proof 
  Induct_on `f` >> simp[subst_def]
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

Theorem ptaut_AND2[simp]:
  ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 1))
Proof 
  simp[ptaut_def, IMP_def, AND_def]
QED 

Theorem ptaut_AND1[simp]:
  ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 0))
Proof 
  simp[ptaut_def, IMP_def, AND_def]
QED 

Theorem ptaut_A_OR_NOT_A[simp]:
  ptaut (DISJ (VAR 0) (NOT(VAR 0)))
Proof 
 simp[ptaut_def]
QED 

Theorem ptaut_NOT_A_OR_A[simp]:
  ptaut (DISJ (NOT(VAR 0)) (VAR 0))
Proof 
 simp[ptaut_def]
QED

Theorem gttExt:
  gtt Ax G f ⇒ gtt (Ax ∪ Ext) G f
Proof
  Induct_on `gtt` >> rw[gtt_rules] >> metis_tac[gtt_rules]
QED

Theorem conj1:
  gtt KAxioms G (AND A B) ⇒ gtt KAxioms G A
Proof 
  `ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 0))` by rw[ptaut_AND1] >>
  `(IMP (AND (VAR 0) (VAR 1)) (VAR 0)) ∈ {a | ptaut a}` by simp[] >>
  `subst (λs. if s = 0 then A else B) (IMP (AND (VAR 0) (VAR 1)) (VAR 0)) = (IMP (AND A B) A)` 
    by simp[subst_def, AND_def, IMP_def] >>
  rw[] >> `gtt KAxioms G (subst (λs. if s = 0 then A else B) (AND (VAR 0) (VAR 1) -> VAR 0))` 
   by simp[gtt_rules, KAxioms_def, CPLAxioms_def] >>
  `gtt KAxioms G (IMP (AND A B) A)` by rfs[] >>
  metis_tac[gtt_rules]
QED 

Theorem conj2:
  gtt KAxioms G (AND A B) ⇒ gtt KAxioms G B
Proof 
  `ptaut (IMP (AND (VAR 0) (VAR 1)) (VAR 1))` by rw[ptaut_AND2] >>
  `(IMP (AND (VAR 0) (VAR 1)) (VAR 1)) ∈ {a | ptaut a}` by simp[] >>
  `subst (λs. if s = 0 then A else B) (IMP (AND (VAR 0) (VAR 1)) (VAR 1)) = (IMP (AND A B) B)` 
    by simp[subst_def, AND_def, IMP_def] >>
  rw[] >> `gtt KAxioms G (subst (λs. if s = 0 then A else B) (AND (VAR 0) (VAR 1) -> VAR 1))` 
   by simp[gtt_rules, KAxioms_def, CPLAxioms_def] >>
  `gtt KAxioms G (IMP (AND A B) B)` by rfs[] >>
  metis_tac[gtt_rules]
QED 

Theorem gttDoubleImp:
  gtt KAxioms G (DOUBLE_IMP A B) ⇒ (gtt KAxioms G A ⇔ gtt KAxioms G B)
Proof 
  rw[DOUBLE_IMP_def] >> rw[EQ_IMP_THM] >> fs[]
  >- (`gtt KAxioms G (A -> B)` by metis_tac[conj1] >> metis_tac[gtt_rules])
  >> `gtt KAxioms G (B -> A)` by metis_tac[conj2] >> metis_tac[gtt_rules]
QED


Theorem gtt_not_not:
  gtt KAxioms G (A -> ¬¬A)
Proof 
  rw[IMP_def] >> Cases_on `A`

  `ptaut (DISJ (VAR 0) (¬(VAR 0)))` by rw[ptaut_A_OR_NOT_A] >>
  cheat
QED 


(*
val subst_def =
  Define
    `subst f FALSE = FALSE /\
     subst f (VAR p) = f p /\
     subst f (DISJ form1 form2) = DISJ (subst f form1) (subst f form2) /\
     subst f (NOT form) = NOT (subst f form) /\
     subst f (DIAM form) = DIAM (subst f form)`;

val peval_def = Define`
    peval σ (VAR p) = σ p /\
    (peval σ (DISJ f1 f2) <=> peval σ f1 \/ peval σ f2) /\
    peval σ FALSE = F /\
    peval σ (NOT f) = ¬peval σ f /\
    peval σ (DIAM f) = F`;

val _ = export_rewrites["peval_def"]

val ptaut_def = Define`
    ptaut f <=> propform f /\ !σ. peval σ f = T`;
*)

(* MIGHT DELETE 
Theorem ptaut_DIAM[simp]:
  ptaut (DIAM f) = F
Proof 
  rw[ptaut_def, peval_def]
QED
*)

Theorem gTk:
 ∀(p :num form list). (KGproof Ax p) ⇒ (∀f. (MEM f p) ⇒ gtt (Ax ∪ KAxioms) ∅ f)
Proof
  Induct_on `KGproof` >> rw[]
  >- metis_tac[]
  >- metis_tac[gtt_rules]
  >- metis_tac[]
  >- metis_tac[gttEmpG] 
  >- simp[]
  >- rw[gtt_rules]
  >- simp[]
  (* K axioms *)
  >- (`subst (λs. if s = 0 then form1 else form2)
        (□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1))
        = (□ (form1 -> form2) -> □ form1 -> □ form2) ` by simp[] >>
        `(□ (VAR 0 -> VAR 1) -> □ (VAR 0) -> □ (VAR 1)) ∈ (Ax ∪ KAxioms)` by simp[KAxioms_def] >>
      metis_tac[gtt_rules]) 
  >- simp[]
  >- (rw[gtt_rules, KAxioms_def, CPLAxioms_def] >> 
      rw[IMP_def] >> 
      >> rw[ptaut_def]
  )
  >- simp[]
  >- rw[BOX_def] >> cheat (*box and diamond*)
  >- (rw[subst_self, subst_def, gtt_rules, KAxioms_def, CPLAxioms_def] >> 
    rw[] >> cheat)
 (* `gtt (Ax ∪ KAxioms) ∅ (subst s f)` suffices_by rw[subst_self]
  simp[KAxioms_def, CPLAxioms_def, gtt_rules]*)
  >- simp[]
  >> rw[gttAx]
  (*>- (first_x_assum drule >>  qmatch_abbrev_tac`gtt Ax G f ⇒ gtt Ax G (subst s f)` >> rw[gttSubst])
*)
QED


Theorem kTg:
  (∀f ∈ p. gtt (Ax ∪ KAxioms) ∅ f) ⇒ ∀Ax p. KGproof Ax p
Proof 

QED

val _ = export_theory()
