import ModalProofChecker

------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------- Proof examples ----------------------------------------------------

correct_proof :: Proof
correct_proof = Proof system_k [( 
        AtomF "p" `ImpF` (AtomF "q" `ImpF` AtomF "p" `AndF` AtomF "q"), 
        Taut
    ),(
        BoxF (AtomF "p" `ImpF` (AtomF "q" `ImpF` (AtomF "p" `AndF` AtomF "q"))),
        Gen 1
    ),(
        BoxF (AtomF "p" `ImpF` AtomF "q") `ImpF` (BoxF (AtomF "p") `ImpF` BoxF (AtomF "q")),
        KAxiom
    ),(
        BoxF (AtomF "p" `ImpF` (AtomF "q" `ImpF` AtomF "p" `AndF` AtomF "q")) `ImpF` 
        ((BoxF (AtomF "p")) `ImpF` BoxF (AtomF "q" `ImpF` AtomF "p" `AndF` AtomF "q")),
        US 3
    ),(
        (BoxF (AtomF "p")) `ImpF` BoxF (AtomF "q" `ImpF` AtomF "p" `AndF` AtomF "q"),
        MP 2 4
    )]

wrong_mp_proof :: Proof
wrong_mp_proof = 
    Proof (Axioms [
        AtomF "p", 
        AtomF "q" `ImpF` AtomF "p"
    ])  
    [(
        AtomF "p", 
        Axiom 1
    ),(
        AtomF "q" `ImpF` AtomF "p", 
        Axiom 2
    ),(
        AtomF "q", 
        MP 1 2
    )]

wrong_tautology_proof :: Proof
wrong_tautology_proof = 
    Proof system_k4 [(
        NotF (AtomF "p") `OrF` AtomF "q", 
        Taut
    )]

wrong_axiom_proof :: Proof
wrong_axiom_proof = 
    Proof system_k [(
        axiom_k, 
        KAxiom
    ),(
        axiom_4, 
        DualAxiom
    )]










wrong_proof_ind_axiom_small :: Proof
wrong_proof_ind_axiom_small = 
    Proof system_k4 [
        (axiom_4, Axiom 0)
    ]

wrong_proof_ind_axiom_big :: Proof
wrong_proof_ind_axiom_big = 
    Proof system_k [
        (axiom_4, Axiom 1)
    ]

wrong_proof_ind_form_small :: Proof
wrong_proof_ind_form_small = 
    Proof (Axioms [
        AtomF "p", 
        AtomF "q" `ImpF` AtomF "p"
    ])
    [(
        AtomF "p", 
        Axiom 1
    ),(
        AtomF "q" `ImpF` AtomF "p", 
        Axiom 2
    ),(
        AtomF "q", 
        MP 0 2
    )]

wrong_proof_ind_form_big :: Proof
wrong_proof_ind_form_big = 
    Proof (Axioms [
        AtomF "p", 
        AtomF "q" `ImpF` AtomF "p"
    ]) 
    [(
        AtomF "p", 
        Axiom 1
    ),(
        AtomF "q" `ImpF` AtomF "p", 
        Axiom 2
    ),(
        AtomF "q", 
        MP 1 3
    )]

wrong_proof_modal_operator_in_tautology :: Proof
wrong_proof_modal_operator_in_tautology = 
    Proof system_k4 [(
        NotF (BoxF (AtomF "p")), 
        Taut
    )]

wrong_sub_proof :: Proof
wrong_sub_proof = 
    Proof system_k [(
        AtomF "p" `OrF` NotF (AtomF "p"), 
        Taut
    ),(
        AtomF "p", 
        US 1
    )]

wrong_usub_proof :: Proof
wrong_usub_proof = 
    Proof system_k [(
        AtomF "p" `OrF` NotF (AtomF "p"), 
        Taut
    ),(
        AtomF "p" `OrF` NotF (AtomF "q"), 
        US 1
    )]

wrong_gen_proof :: Proof
wrong_gen_proof = 
    Proof system_k [(
        AtomF "p" `EqvF` NotF (NotF (AtomF "p")), 
        Taut
    ),(
        BoxF (AtomF "p"), 
        Gen 1
    )]









------------------------------------------- Testing ModalProofChecker module -------------------------------------------

all_proofs :: [Proof]
all_proofs = [
        correct_proof,
        wrong_proof_ind_axiom_small,
        wrong_proof_ind_axiom_big,
        wrong_proof_ind_form_small,
        wrong_proof_ind_form_big,
        wrong_axiom_proof, 
        wrong_proof_modal_operator_in_tautology,
        wrong_tautology_proof, 
        wrong_mp_proof,
        wrong_sub_proof,
        wrong_usub_proof,
        wrong_gen_proof
    ]

test_ModalProofChecker :: Bool
test_ModalProofChecker = 
    let
        correct_answers = [
                (True, []),
                (False,[
                    "WRONG! Found a mistake in deduction 1.",
                    "Reason: The index of the axiom should be a positive integer."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 1.",
                    "Reason: The index of the axiom is bigger than the number of axioms from the system."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 3.",
                    "Reason: The index of the formula on which the rule is applied should be a positive integer."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 3.",
                    "Reason: The index of the formula on which the rule is applied should be\
                           \ smaller than the index of the formula that is being proven."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 2.",
                    "Reason: The formula is not an instance of the given axiom.",
                    "Reason: Couldn't determine a substitution function for the given formulas."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 1.",
                    "Reason: A proven tautology should not contain any modal operators (BoxF or DiaF)."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 1.",
                    "Reason: The given propositional formula is not a tautology.\
                           \ It can be falsified by the following labelling function { p:True, q:False }."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 3.",
                    "Reason: The modus ponens rule was not applied correctly on the given formulas."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 2.",
                    "Reason: Couldn't determine a substitution function for the given formulas."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 2.",
                    "Reason: Found a substitution, but it is not uniform. The substitution used MUST be uniform."
                    ]),
                (False,[
                    "WRONG! Found a mistake in deduction 2.",
                    "Reason: The generalisation rule was not applied correctly on the given formula."
                    ])
            ]
    in
        map verify_proof all_proofs == correct_answers

proof_results :: [(Bool, [String])]
proof_results =
    map verify_proof all_proofs
  
    