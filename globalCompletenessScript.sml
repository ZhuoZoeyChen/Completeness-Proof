open HolKernel Parse boolLib bossLib;
open nlistTheory listTheory;
open pred_setTheory;
open chap1Theory;

val _ = new_theory "globalCompleteness";

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

Theorem gTk:
 ∀(p :num form list). (KGproof Ax p) ⇒ (∀f. (MEM f p)  ⇒ gtt (Ax ∪ KAxioms) ∅ f)
Proof
  Induct_on `KGproof` >> rw[]
  >- metis_tac[]
  >- metis_tac[gtt_rules]
  >- metis_tac[]
  >- metis_tac[gttEmpG] 
  >- simp[]
  >- rw[gtt_rules]
  >- simp[]
  >- (rw[KAxioms_def, gtt_rules, gttAx] >> cheat) (* K Axiom*)
  >- simp[]
  >- cheat (* Diamond and box *)
  >- simp[]
  >- cheat (*box and diamond*)
  >- (rw[subst_self, subst_def, gtt_rules, KAxioms_def, CPLAxioms_def] >> cheat)
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