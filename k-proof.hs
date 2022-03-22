import Data.Bool
import Data.List

-- Defining the elements of a modal logic
type Atom = String
data Formula = F | T
               | AtomF Atom
               | NotF Formula 
               | AndF Formula Formula
               | OrF Formula Formula
               | ImpF Formula Formula
               | EqvF Formula Formula
               | BoxF Formula
               | DiaF Formula
               | ErrorF
               deriving(Show, Eq)
type World = String
type Relation = [(World,World)]
type LabelFunction = [(World, [Atom])]
data Model = Model [World] Relation LabelFunction
data Frame = Frame [World] Relation

-- Defining the elements for writing proofs for modal logic
data Deduction_System = Axioms { get_axioms :: [Formula]}
                        deriving Show
data Deduction_Rule = Axiom Int     -- We used an axiom of the system
                      | Taut        -- We used a tautology
                      | MP Int Int  -- We deduced the formula 
                                    -- by applying the Modus Ponens rule
                      | US Int      -- We applyed a universal substitution 
                                    -- to obtain the formula
                      | Gen Int     -- We obtained the formula by generalization 
                      deriving Show
data Proof = Proof Deduction_System [(Formula, Deduction_Rule)]
             deriving Show


-- Defining the common axioms for different modal logic systems 
k_axiom :: Formula
k_axiom = ImpF (BoxF (ImpF (AtomF "phi") (AtomF "psi")))
               (ImpF (BoxF (AtomF "phi")) (BoxF (AtomF "psi")))
dual_axiom :: Formula
dual_axiom = EqvF (DiaF (AtomF "phi")) (NotF (BoxF (NotF (AtomF "phi"))))
tranzitive_axiom :: Formula
tranzitive_axiom = ImpF (BoxF (AtomF "phi")) (BoxF (BoxF (AtomF "phi")))

-- Defining common normal modal logic systems
k_system :: Deduction_System
k_system = Axioms [k_axiom, dual_axiom]
k4_system :: Deduction_System
k4_system = Axioms [k_axiom, dual_axiom, tranzitive_axiom]


-- Verifying a modal logic proof
verify_proof :: Proof -> Bool
verify_proof (Proof (Axioms axs) []) = True
verify_proof (Proof (Axioms axs) fs) = 
    let
        first_deductions = verify_proof (Proof (Axioms axs) (init fs))
        current_deduction = verify_deduction axs (init fs) (snd.last $ fs) (fst.last $ fs)
    in
        if first_deductions && not current_deduction
        then error $ "Deduction " ++ (show (length(fs) - 1)) ++ " is wrong."
        else first_deductions && current_deduction


verify_deduction :: [Formula] 
                 -> [(Formula, Deduction_Rule)] 
                 -> Deduction_Rule 
                 -> Formula 
                 -> Bool
verify_deduction axs _ (Axiom ax1) form = verify_axiom (axs !! ax1) form
verify_deduction _ _ (Taut) form = verify_tautology form
verify_deduction _ pforms (MP f1 f2) form = 
    verify_mp (fst $ pforms !! f1) (fst $ pforms !! f2) form
verify_deduction _ pforms (US f1) form = verify_usubs (fst $ pforms !! f1) form
verify_deduction _ pforms (Gen f1) form = verify_gen (fst $ pforms !! f1) form


verify_axiom :: Formula -> Formula -> Bool
verify_axiom axiom_form form = verify_usubs axiom_form form

verify_tautology :: Formula -> Bool
verify_tautology form = 
    truth_table (get_evaluations.get_atoms $ form) form
truth_table :: [[(Atom, Bool)]] -> Formula -> Bool
truth_table (eval:evals) form = 
    (truth_table_eval eval form) && (truth_table evals form)
truth_table [] form = True
truth_table_eval :: [(Atom, Bool)] -> Formula -> Bool
truth_table_eval eval F = False
truth_table_eval eval T = True
truth_table_eval eval (AtomF atom) = head [snd x| x <- eval, fst x == atom]
truth_table_eval eval (NotF form) = not $ truth_table_eval eval form
truth_table_eval eval (AndF f1 f2) = 
    truth_table_eval eval f1 && truth_table_eval eval f2
truth_table_eval eval (OrF f1 f2) =
    truth_table_eval eval f1 || truth_table_eval eval f2
truth_table_eval eval (ImpF f1 f2) =
    if (truth_table_eval eval f1)
    then (truth_table_eval eval f2)
    else True
truth_table_eval eval (EqvF f1 f2) =
    truth_table_eval eval f1 == truth_table_eval eval f2
truth_table_eval eval _ = False
get_atoms :: Formula -> [Atom]
get_atoms F = []
get_atoms T = []
get_atoms (AtomF atom) = [atom]
get_atoms (NotF form) = get_atoms form
get_atoms (AndF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (OrF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (ImpF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (EqvF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (BoxF f1) = get_atoms f1
get_atoms (DiaF f1) = get_atoms f1
get_evaluations :: [Atom] -> [[(Atom, Bool)]]
get_evaluations (atom:atoms) = 
    [(atom,False):eval | eval <- get_evaluations atoms] ++
    [(atom,True):eval | eval <- get_evaluations atoms]
get_evaluations [] = [[]]

verify_mp :: Formula -> Formula -> Formula -> Bool
verify_mp f1 (ImpF f2 f3) form = f1 == f2 && f3 == form
verify_mp (ImpF f1 f2) f3 form = f1 == f3 && f2 == form
verify_mp _ _ _ = False

verify_usubs :: Formula -> Formula -> Bool
verify_usubs f form = 
    let 
        subs = build_substitution f form
        valid_subs = check_substitution subs
        subs_f = make_substitution subs f
    in
        valid_subs && subs_f == form
build_substitution :: Formula -> Formula -> [(Atom, Formula)]
build_substitution F F = []
build_substitution T T = []
build_substitution (AtomF atom) form = [(atom, form)]
build_substitution (NotF f1) (NotF f2) = build_substitution f1 f2
build_substitution (AndF f1 f2) (AndF f3 f4) =
    build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (OrF f1 f2) (OrF f3 f4) =
    build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (ImpF f1 f2) (ImpF f3 f4) =
    build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (EqvF f1 f2) (EqvF f3 f4) =
    build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (BoxF f1) (BoxF f2) = build_substitution f1 f2
build_substitution (DiaF f1) (DiaF f2) = build_substitution f1 f2
build_substitution _ _ = [("", ErrorF)]
check_substitution :: [(Atom, Formula)] -> Bool
check_substitution subs = 
    let
        has_error = elem ErrorF (map snd subs)
        has_no_contradictions = 
            let unique_atom_subs = map fst (nub subs)
            in nub(unique_atom_subs) == unique_atom_subs
    in
        not has_error && has_no_contradictions
make_substitution :: [(Atom, Formula)] -> Formula -> Formula
make_substitution subs F = F
make_substitution subs T = T
make_substitution subs (AtomF atom) = 
    snd.head $ filter (\(at, _) -> at == atom) subs
make_substitution subs (AndF f1 f2) =
    let 
        subs_f1 = make_substitution subs f1
        subs_f2 = make_substitution subs f2
    in
        AndF subs_f1 subs_f2
make_substitution subs (OrF f1 f2) =
    let 
        subs_f1 = make_substitution subs f1
        subs_f2 = make_substitution subs f2
    in
        OrF subs_f1 subs_f2
make_substitution subs (ImpF f1 f2) =
    let 
        subs_f1 = make_substitution subs f1
        subs_f2 = make_substitution subs f2
    in
        ImpF subs_f1 subs_f2
make_substitution subs (EqvF f1 f2) =
    let 
        subs_f1 = make_substitution subs f1
        subs_f2 = make_substitution subs f2
    in
        EqvF subs_f1 subs_f2
make_substitution subs (BoxF f1) = BoxF (make_substitution subs f1)
make_substitution subs (DiaF f1) = DiaF (make_substitution subs f1)

verify_gen :: Formula -> Formula -> Bool
verify_gen f form = (BoxF f) == form



-- Examples
deductions_example :: [(Formula, Deduction_Rule)]
deductions_example = 
    [ (ImpF (AtomF "p") (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q"))), Taut)
    , (BoxF (ImpF (AtomF "p") (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q")))), Gen 0)
    , (ImpF (BoxF (ImpF (AtomF "p") (AtomF "q"))) 
            (ImpF (BoxF (AtomF "p")) (BoxF (AtomF "q"))), Axiom 0)
    , (ImpF (BoxF (ImpF (AtomF "p") 
                        (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q"))))) 
            (ImpF (BoxF (AtomF "p")) 
                  (BoxF (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q"))))), US 2)
    , (ImpF (BoxF (AtomF "p")) 
            (BoxF (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q")))), MP 1 3)
    , (ImpF (BoxF (ImpF (AtomF "q") (AndF (AtomF "p") (AtomF "q")))) 
            (ImpF (BoxF (AtomF "q")) (BoxF (AndF (AtomF "p") (AtomF "q")))), US 2)
    ]
proof_example :: Proof
proof_example = Proof k_system deductions_example

wrong_axiom_proof :: Proof
wrong_axiom_proof = Proof k_system [(k_axiom, Axiom 0), (tranzitive_axiom, Axiom 1)]

wrong_tautology_proof :: Proof
wrong_tautology_proof = Proof k4_system [((BoxF (AtomF "p")), Taut)]

wrong_mp_proof :: Proof
wrong_mp_proof = 
    Proof (Axioms [AtomF "p", ImpF (AtomF "q") (AtomF "p")])  
          [(AtomF "p", Axiom 0)
          , (ImpF (AtomF "q") (AtomF "p"), Axiom 1)
          , (AtomF "q", MP 0 1)
          , (AtomF "p", Axiom 0)
          ]

wrong_usub_proof :: Proof
wrong_usub_proof = Proof k_system [(OrF (AtomF "p") (NotF (AtomF "p")), Taut)
                                  , (OrF (AtomF "p") (AtomF "q"), US 0)
                                  ]

wrong_gen_proof :: Proof
wrong_gen_proof = Proof k_system [(EqvF (AtomF "p") (NotF (NotF (AtomF "p"))), Taut)
                                 , (BoxF (AtomF "p"), Gen 0)
                                 ]