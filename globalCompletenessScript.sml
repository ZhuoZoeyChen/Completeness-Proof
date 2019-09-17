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
 

Definition CPLAxioms_def:
CPLAxioms = {A -> (B -> A) | T } ∪ 
            {NOT (NOT A) -> A | T} ∪
            {(A -> (B ->C)) -> ((A -> B) -> (B -> C))| T} 
End


(* add type constraint *)
Definition KAxioms_def:
  KAxioms = CPLAxioms ∪
           {(□ (A -> B)) -> ((□ A) -> (□ B)) | T}
End


fs[]
rw[]
simp[]
metis_tac[]
(* how to make Ax into a parameter gtt takes rather than a universal variable *)
Inductive gtt:
	(∀f. f ∈ G ⇒ gtt Ax G f) ∧
	(∀f. f ∈ Ax ∧ (Ax = CPLAxioms ∨ Ax = KAxioms) ⇒ gtt Ax G f) ∧
	(∀f1 f2. gtt Ax G f1 ∧ gtt Ax G (IMP f1 f2) ⇒ gtt Ax G f2) ∧
	(∀f. gtt Ax G f ⇒ gtt Ax G (□ f))
End

Theorem gttSubst:
 ∀s f. gtt Ax G f ⇒ gtt Ax {subst s g | g ∈ G} (subst s f)
Proof 
  Induct_on `gtt` >> 
  rw[gtt_rules, subst_def] 
    >- (`(subst s f) ∈ {subst s g| g ∈ G}` suffices_by rw[gtt_rules] 
          >> fs[] >> metis_tac[])
    >- (`(subst s f) ∈ CPLAxioms` suffices_by rw[gtt_rules] 
          >> fs[CPLAxioms_def] >> rw[subst_def] >> cheat >> cheat >> cheat)
    >- (`(subst s f) ∈ KAxioms` suffices_by rw[gtt_rules] 
          >> fs[KAxioms_def] >> rw[subst_def] >> cheat)

QED


Theorem gTk:
  ∀(p :'a form list). (KGproof Ax p) ⇒ (∀f. (MEM f p)  ⇒ gtt (Ax ∪ KAxioms) ∅ f)
Proof
  Induct_on `KGproof` >> rw[]
  >- metis_tac[]
  >- metis_tac[gtt_rules]
  >- metis_tac[]
  >- (first_x_assum drule >> )

QED



Theorem kTg:
  (∀f ∈ p. gtt (Ax ∪ KAxioms) ∅ f) ⇒ ∀Ax p. KGproof Ax p
Proof 

QED

val _ = export_theory()