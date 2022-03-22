
module ModalProofChecker where

import Data.Bool
import Data.List
import Control.Monad.Writer


------------------------------------------------------------------------------------------------------------------------
---------------------------------------- Defining the elements of a modal logic ----------------------------------------

type World = String
type Relation = [(World,World)]
type LabelFunction = [(World, [Atom])]
data Model = Model [World] Relation LabelFunction
data Frame = Frame [World] Relation


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
               deriving Eq
infixl 7 `AndF`
infixl 6 `OrF`
infixr 5 `ImpF`
infixr 5 `EqvF`

newtype Deduction_System = Axioms { get_axioms :: [Formula]}
                           deriving Show

data Deduction_Rule = Axiom Int     -- We used an axiom of the system
                      | Taut        -- We used a tautology
                      | KAxiom      -- We used the axiom K
                      | DualAxiom   -- We used the dual axiom
                      | MP Int Int  -- We deduced the formula by applying the Modus Ponens rule
                      | US Int      -- We applyed a universal substitution to obtain the formula
                      | Gen Int     -- We obtained the formula by generalization
                      deriving Show

data Proof = Proof Deduction_System [(Formula, Deduction_Rule)]

data PropLabelFunction = LabelFunc [(Atom, Bool)]



--------------------------------------- Printing functions for previous elements ---------------------------------------

-- not_symbol = "\x00AC "
-- and_symbol = " /\\ "
not_symbol = "not "
box_symbol = "\x25FB "
diamond_symbol = "\x25C7 "
and_symbol = "  \x2227  "
or_symbol = "  \x2228  "
imp_symbol = "  \x2192  "
eqv_symbol = "  \x2194  "

-- The function for displaying formulas
-- Evaluates each case to remove the redundant parentheses
instance Show Formula where
    show F = "F"
    show T = "T"
    show (AtomF atom) = atom

    show (NotF (BoxF formula)) = not_symbol ++ show (BoxF formula)
    show (NotF (DiaF formula)) = not_symbol ++ show (DiaF formula)
    show (NotF (NotF formula)) = not_symbol ++ show (NotF formula)
    show (NotF (AtomF atom)) = not_symbol ++ show (AtomF atom)
    show (NotF F) = not_symbol ++ show F
    show (NotF T) = not_symbol ++ show T
    show (NotF formula) = not_symbol ++ "(" ++ show formula ++ ")"

    show (BoxF (BoxF formula)) = box_symbol ++ show (BoxF formula)
    show (BoxF (DiaF formula)) = box_symbol ++ show (DiaF formula)
    show (BoxF (NotF formula)) = box_symbol ++ show (NotF formula)
    show (BoxF (AtomF atom)) = box_symbol ++ show (AtomF atom)
    show (BoxF F) = box_symbol ++ show F
    show (BoxF T) = box_symbol ++ show T
    show (BoxF formula) = box_symbol ++ "(" ++ show formula ++ ")"

    show (DiaF (BoxF formula)) = diamond_symbol ++ show (BoxF formula)
    show (DiaF (DiaF formula)) = diamond_symbol ++ show (DiaF formula)
    show (DiaF (NotF formula)) = diamond_symbol ++ show (NotF formula)
    show (DiaF (AtomF atom)) = diamond_symbol ++ show (AtomF atom)
    show (DiaF F) = diamond_symbol ++ show F
    show (DiaF T) = diamond_symbol ++ show T
    show (DiaF formula) = diamond_symbol ++ "(" ++ show formula ++ ")"

    show (AndF (OrF formula1 formula2) (OrF formula3 formula4)) = "(" ++ show (OrF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (OrF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (OrF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (OrF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (OrF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (OrF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (ImpF formula1 formula2) (OrF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (OrF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (ImpF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (ImpF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (EqvF formula1 formula2) (OrF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (OrF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (EqvF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (EqvF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  and_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (AndF (OrF formula1 formula2) formula3) = "(" ++ show (OrF formula1 formula2) ++ ")" ++ and_symbol ++ 
                                                   show formula3
    show (AndF formula1 (OrF formula2 formula3)) = show formula1 ++ and_symbol ++ "(" ++ show (OrF formula2 formula3) ++ 
                                                   ")"
    show (AndF (ImpF formula1 formula2) formula3) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ and_symbol ++ 
                                                   show formula3
    show (AndF formula1 (ImpF formula2 formula3)) = show formula1 ++ and_symbol ++ "(" ++ show (ImpF formula2 formula3) 
                                                    ++ ")"    
    show (AndF (EqvF formula1 formula2) formula3) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ and_symbol ++ 
                                                   show formula3
    show (AndF formula1 (EqvF formula2 formula3)) = show formula1 ++ and_symbol ++ "(" ++ show (EqvF formula2 formula3) 
                                                    ++ ")"
    show (AndF formula1 formula2) = show formula1 ++ and_symbol ++ show formula2

    show (OrF (ImpF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  or_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (OrF (ImpF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  or_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (OrF (EqvF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  or_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (OrF (EqvF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  or_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (OrF (ImpF formula1 formula2) formula3) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ or_symbol ++ 
                                                   show formula3
    show (OrF formula1 (ImpF formula2 formula3)) = show formula1 ++ or_symbol ++ "(" ++ show (ImpF formula2 formula3) 
                                                    ++ ")"    
    show (OrF (EqvF formula1 formula2) formula3) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ or_symbol ++ 
                                                   show formula3
    show (OrF formula1 (EqvF formula2 formula3)) = show formula1 ++ or_symbol ++ "(" ++ show (EqvF formula2 formula3) 
                                                    ++ ")"
    show (OrF formula1 formula2) = show formula1 ++ or_symbol ++ show formula2

    show (ImpF (ImpF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  imp_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (ImpF (ImpF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  imp_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (ImpF (EqvF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  imp_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (ImpF (EqvF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  imp_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (ImpF (ImpF formula1 formula2) formula3) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ imp_symbol ++ 
                                                   show formula3
    show (ImpF formula1 (ImpF formula2 formula3)) = show formula1 ++ imp_symbol ++ "(" ++ show (ImpF formula2 formula3) 
                                                    ++ ")"    
    show (ImpF (EqvF formula1 formula2) formula3) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ imp_symbol ++ 
                                                   show formula3
    show (ImpF formula1 (EqvF formula2 formula3)) = show formula1 ++ imp_symbol ++ "(" ++ show (EqvF formula2 formula3) 
                                                    ++ ")"
    show (ImpF formula1 formula2) = show formula1 ++ imp_symbol ++ show formula2

    show (EqvF (ImpF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  eqv_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (EqvF (ImpF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ 
                                                                  eqv_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (EqvF (EqvF formula1 formula2) (ImpF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  eqv_symbol ++ "(" ++ show (ImpF formula3 formula4) ++ 
                                                                  ")"
    show (EqvF (EqvF formula1 formula2) (EqvF formula3 formula4)) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ 
                                                                  eqv_symbol ++ "(" ++ show (EqvF formula3 formula4) ++ 
                                                                  ")"
    show (EqvF (ImpF formula1 formula2) formula3) = "(" ++ show (ImpF formula1 formula2) ++ ")" ++ eqv_symbol ++ 
                                                   show formula3
    show (EqvF formula1 (ImpF formula2 formula3)) = show formula1 ++ eqv_symbol ++ "(" ++ show (ImpF formula2 formula3) 
                                                    ++ ")"    
    show (EqvF (EqvF formula1 formula2) formula3) = "(" ++ show (EqvF formula1 formula2) ++ ")" ++ eqv_symbol ++ 
                                                   show formula3
    show (EqvF formula1 (EqvF formula2 formula3)) = show formula1 ++ eqv_symbol ++ "(" ++ show (EqvF formula2 formula3) 
                                                    ++ ")"
    show (EqvF formula1 formula2) = show formula1 ++ eqv_symbol ++ show formula2

-- Functions for printing a proof
showDeduction :: Int -> Formula -> Deduction_Rule -> String
showDeduction idx form Taut = "\t" ++ (show idx) ++ ". " ++ (show Taut) ++ "\t\t" ++ (show form) ++ "\n"
showDeduction idx form (US ind) = "\t" ++ (show idx) ++ ". " ++ (show (US ind)) ++ "\t\t" ++ (show form) ++ "\n"
showDeduction idx form ded_rule = "\t" ++ (show idx) ++ ". " ++ (show ded_rule) ++ "\t" ++ (show form) ++ "\n"

showDeductions :: [(Formula, Deduction_Rule)] -> String
showDeductions deductions = "Steps of the proof:\n" ++ 
    (foldl (++) "" [
        (showDeduction idx form ded_rule) |
        (idx,(form, ded_rule)) <- zip [1..] deductions
    ])

showAxioms :: [Formula] -> String
showAxioms axioms = foldl (++) "" ["\t" ++ (show idx) ++ ". " ++ (show form) ++ "\n" | (idx, form)<-zip [1..] axioms]

instance Show Proof where
    show (Proof (Axioms []) deductions) = "\nK system (no additional axioms)\n" ++ (showDeductions deductions)
    show (Proof (Axioms axs) deductions) = "\nAxioms of the system: \n" ++ (showAxioms axs) ++ (showDeductions deductions)

-- Prints a labelling function recursive
showLabelFunc :: [(Atom, Bool)] -> String
showLabelFunc [] = ""
showLabelFunc ((atom, val):[]) = atom ++ ":" ++ (show val)
showLabelFunc ((atom, val):atoms) = atom ++ ":" ++ (show val) ++ ", " ++ (showLabelFunc  atoms)

instance Show PropLabelFunction where
    show (LabelFunc func) = "{ " ++ (showLabelFunc func) ++ " }"

------------------------------------------------------------------------------------------------------------------------





------------------------------------------------------------------------------------------------------------------------
------------------------------------- Define common axioms and modal logic systems -------------------------------------

axiom_k :: Formula
axiom_k = BoxF (AtomF "p" `ImpF` AtomF "q") `ImpF` (BoxF (AtomF "p") `ImpF` BoxF (AtomF "q"))

axiom_dual :: Formula
axiom_dual = DiaF (AtomF "p") `EqvF` NotF (BoxF (NotF (AtomF "p")))

axiom_4 :: Formula
axiom_4 = BoxF (AtomF "p") `ImpF` BoxF (BoxF (AtomF "p"))

axiom_m :: Formula
axiom_m = BoxF (AtomF "p") `ImpF` AtomF "p"

axiom_d :: Formula
axiom_d = BoxF (AtomF "p") `ImpF` DiaF (AtomF "p")

axiom_b :: Formula
axiom_b = AtomF "p" `ImpF` BoxF (DiaF (AtomF "p"))

axiom_5 :: Formula
axiom_5 = DiaF (AtomF "p") `ImpF` BoxF (DiaF (AtomF "p"))

axiom_cd :: Formula
axiom_cd = DiaF (AtomF "p") `ImpF` BoxF (AtomF "p")

axiom_box_m :: Formula
axiom_box_m = BoxF (BoxF (AtomF "p") `ImpF` AtomF "p")

axiom_c4 :: Formula
axiom_c4 = BoxF (BoxF (AtomF "p")) `ImpF` BoxF (AtomF "p")

axiom_c :: Formula
axiom_c = DiaF (BoxF (AtomF "p")) `ImpF` BoxF (DiaF (AtomF "p"))



system_k :: Deduction_System
system_k = Axioms []

system_k4 :: Deduction_System
system_k4 = Axioms [axiom_4]

system_kt :: Deduction_System
system_kt = Axioms [axiom_m]

system_kb :: Deduction_System
system_kb = Axioms [axiom_5]

system_kd :: Deduction_System
system_kd = Axioms [axiom_d]

system_kd45 :: Deduction_System
system_kd45 = Axioms [axiom_d, axiom_4, axiom_5]

system_s4 :: Deduction_System
system_s4 = Axioms [axiom_m, axiom_4]

system_s5 :: Deduction_System
system_s5 = Axioms [axiom_m, axiom_5]

------------------------------------------------------------------------------------------------------------------------





------------------------------------------------------------------------------------------------------------------------
-------------------------------------------- Functions for verifying proofs --------------------------------------------

-- @argument Int represents the index of the wrong deduction
-- @return String returns a message that signal a mistake
wrong_deduction_message :: Int -> String
wrong_deduction_message index = "WRONG! Found a mistake in deduction " ++ (show index) ++ "."

-- @argument Proof represents the demonstration which we want to check
-- @return Bool returns if the proof is correct (True) or incorrect (False)
-- @return [String] returns in case of error a list of error messages which details the error
verify_proof :: Proof -> (Bool, [String])
verify_proof proof = 
    let 
        (is_correct, messages) = runWriter $ verify_proof_recursive proof
    in
        (is_correct, reverse messages)

-- @argument Proof represents the demonstration which we want to check
-- @return Writer [String] Bool returns if demonstration is correct or not and in case of error, an error stack messages
verify_proof_recursive :: Proof -> Writer [String] Bool
verify_proof_recursive (Proof ded_system []) = return True
verify_proof_recursive (Proof ded_system fs) = 
    verify_proof_recursive (Proof ded_system (init fs)) >>= (\are_previous_deductions_correct ->
        if not are_previous_deductions_correct
        then return False
        else
            verify_deduction (get_axioms ded_system) (map fst $ init fs) 
                             (fst.last $ fs) (snd.last $ fs) >>= (\is_current_deduction_correct -> 
                if is_current_deduction_correct
                then return True
                else writer (False, [wrong_deduction_message $ length fs])
            )
                
    )

------------------------------------------------------------------------------------------------------------------------
------------------------------- Defining the messages that detail the reason of an error -------------------------------

reason_index_axiom_too_small :: String
reason_index_axiom_too_small = 
    "Reason: The index of the axiom should be a positive integer."

reason_index_axiom_too_big :: String
reason_index_axiom_too_big = 
    "Reason: The index of the axiom is bigger than the number of axioms from the system."

reason_index_formula_too_small :: String
reason_index_formula_too_small = 
    "Reason: The index of the formula on which the rule is applied should be a positive integer."

reason_index_formula_too_big :: String
reason_index_formula_too_big = 
    "Reason: The index of the formula on which the rule is applied should be smaller\
           \ than the index of the formula that is being proven."

reason_no_instance_axiom :: String
reason_no_instance_axiom =
    "Reason: The formula is not an instance of the given axiom."

reason_modal_operator_in_tautology :: String
reason_modal_operator_in_tautology = 
    "Reason: A proven tautology should not contain any modal operators (BoxF or DiaF)."

reason_no_tautology :: PropLabelFunction -> String
reason_no_tautology eval = 
    "Reason: The given propositional formula is not a tautology.\ 
           \ It can be falsified by the following labelling function " ++ (show eval) ++ "." 

reason_wrong_modus_ponens :: String
reason_wrong_modus_ponens = 
    "Reason: The modus ponens rule was not applied correctly on the given formulas."

reason_no_substitution :: String
reason_no_substitution =
    "Reason: Couldn't determine a substitution function for the given formulas."

reason_no_uniform_substitution :: String
reason_no_uniform_substitution = 
    "Reason: Found a substitution, but it is not uniform. The substitution used MUST be uniform."

reason_wrong_generalisation :: String
reason_wrong_generalisation = 
    "Reason: The generalisation rule was not applied correctly on the given formula."


---------------------------------------- Functions for verifying only deduction ----------------------------------------

-- @argument [Formula] represents the axiom of the system that we considered
-- @argument [Formula] represents the formula proven until now 
-- @argument Formula represents the formula whose proof is checked at the current step
-- @argument Deduction_Rule represents the deduction rule and the formulas used to prove the current formula
-- @return Bool returns if the current formula was correctly obtained by applying the mentioned deduction rule
verify_deduction :: [Formula] -> [Formula]-> Formula -> Deduction_Rule -> Writer [String] Bool
verify_deduction axioms _ curr_formula (Axiom ind_axiom) = 
    if ind_axiom < 1 then writer (False, [reason_index_axiom_too_small])
    else 
        if ind_axiom > length axioms then writer (False, [reason_index_axiom_too_big])
        else verify_axiom (axioms !! (ind_axiom-1)) curr_formula
verify_deduction _ _ curr_formula (Taut) = verify_tautology curr_formula
verify_deduction _ _ curr_formula (KAxiom) = verify_axiom axiom_k curr_formula
verify_deduction _ _ curr_formula (DualAxiom) = verify_axiom axiom_dual curr_formula
verify_deduction _ forms curr_formula (MP ind_form1 ind_form2) = 
    if ind_form1 < 1 || ind_form2 < 1 then writer (False, [reason_index_formula_too_small])
    else 
        if ind_form1 > length forms || ind_form2 > length forms then writer (False, [reason_index_formula_too_big])
        else 
            if verify_mp (forms !! (ind_form1-1)) (forms !! (ind_form2-1)) curr_formula then return True
            else writer (False, [reason_wrong_modus_ponens])
verify_deduction _ forms curr_formula (US ind_form) = 
    if ind_form < 1 then writer (False, [reason_index_formula_too_small])
    else 
        if ind_form > length forms then writer (False, [reason_index_formula_too_big])
        else verify_usubs (forms !! (ind_form-1)) curr_formula
verify_deduction _ forms curr_formula (Gen ind_form) =
    if ind_form < 1 then writer (False, [reason_index_formula_too_small])
    else 
        if ind_form > length forms then writer (False, [reason_index_formula_too_big])
        else 
            if verify_gen (forms !! (ind_form-1)) curr_formula then return True
            else writer (False, [reason_wrong_generalisation])

------------------------------------------------------------------------------------------------------------------------
-- @argument Formula represents the axiom of the system
-- @argument Formula represents the formula proven because it is an instance of an axiom
-- @return Bool returns if the rule was applied correctly
verify_axiom :: Formula -> Formula -> Writer [String] Bool
verify_axiom axiom_form form = 
    verify_usubs axiom_form form >>= (\is_instance_of_axiom -> 
        if is_instance_of_axiom
        then return True
        else writer (False, [reason_no_instance_axiom])
    )

------------------------------------------------------------------------------------------------------------------------
-- @argument Formula represents the formula proven because it is a tatutology
-- @return Bool returns if the rule was applied correctly
verify_tautology :: Formula -> Writer [String] Bool
verify_tautology form = 
    if not $ is_propositional_formula form
    then writer (False, [reason_modal_operator_in_tautology])
    else  
        let 
            labelling_functions = map LabelFunc $ get_evaluations.get_atoms $ form
        in
            truth_table labelling_functions form
             

-- @argument Formula represents the formula proven because it is a tautology from propositional logic
-- @return Bool returns if the formula is from the propositional logic
is_propositional_formula :: Formula -> Bool
is_propositional_formula F = True
is_propositional_formula T = True
is_propositional_formula (AtomF atom) = True
is_propositional_formula (NotF form) = is_propositional_formula form
is_propositional_formula (AndF f1 f2) = is_propositional_formula f1 && is_propositional_formula f2
is_propositional_formula (OrF f1 f2) = is_propositional_formula f1 && is_propositional_formula f2
is_propositional_formula (ImpF f1 f2) = is_propositional_formula f1 && is_propositional_formula f2
is_propositional_formula (EqvF f1 f2) = is_propositional_formula f1 && is_propositional_formula f2
is_propositional_formula _ = False

-- @argument [[(Atom, Bool)]] represents the evaluations that weren't checked until now. Each evaluation is represented 
--                            by a list of pair Atom - Bool. The list only contains the atoms relevant for the current 
--                            formula
-- @argument Formula represents the current formula
-- @argument Bool returns if the current formula is a true in all evaluations from the list or not
truth_table :: [PropLabelFunction] -> Formula -> Writer [String] Bool
truth_table [] form = return True
truth_table (eval:evals) form = 
    if not $ evaluation eval form 
    then writer (False, [reason_no_tautology eval])
    else truth_table evals form

-- @argument [(Atom, Bool)] represents an evaluation in the some format described at the previous function
-- @argument represents the current formula
-- @return Bool returns if the current formula is true when evaluated with the given labelling function
evaluation :: PropLabelFunction -> Formula -> Bool
evaluation (LabelFunc eval) F = False
evaluation (LabelFunc eval) T = True
evaluation (LabelFunc eval) (AtomF atom) = head [value | (at, value) <- eval, at == atom]
evaluation eval (NotF form) = not $ evaluation eval form
evaluation eval (AndF f1 f2) = evaluation eval f1 && evaluation eval f2
evaluation eval (OrF f1 f2) = evaluation eval f1 || evaluation eval f2
evaluation eval (ImpF f1 f2) = if (evaluation eval f1) then (evaluation eval f2) else True
evaluation eval (EqvF f1 f2) = evaluation eval f1 == evaluation eval f2

-- @argument Formula represents a formula from the modal logic
-- @return [Atom] returns a list of the propositional atoms found in the received formula
get_atoms :: Formula -> [Atom]
get_atoms F = []
get_atoms T = []
get_atoms (AtomF atom) = [atom]
get_atoms (NotF form) = get_atoms form
get_atoms (AndF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (OrF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (ImpF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (EqvF f1 f2) = nub $ (get_atoms f1) ++ (get_atoms f2)
get_atoms (BoxF form) = get_atoms form
get_atoms (DiaF form) = get_atoms form

-- @argument [Atom] represents a list of atoms contained by a formula
-- @return [[(Atom, Bool)]] returns a list of evaluations. Each evaluations contains only values for the given atoms
get_evaluations :: [Atom] -> [[(Atom, Bool)]]
get_evaluations [] = [[]]
get_evaluations (atom:atoms) = [(atom,False):eval | eval <- get_evaluations atoms] ++ 
                               [(atom,True):eval | eval <- get_evaluations atoms]

------------------------------------------------------------------------------------------------------------------------
-- @argument Formula represents the first formula used by the modus ponens rule
-- @argument Formula represents the second formula used by the modus ponens rule
-- @argument Formula represents the formula proven by applying modus ponens on the first two formulas
-- @return Bool returns if the rule was applied correctly
verify_mp :: Formula -> Formula -> Formula -> Bool
verify_mp (ImpF f1 f2) (ImpF f3 f4) form = 
    (ImpF f1 f2) == f3 && f4 == form || 
    (ImpF f3 f4) == f1 && f2 == form
verify_mp f1 (ImpF f2 f3) form = f1 == f2 && f3 == form
verify_mp (ImpF f1 f2) f3 form = f1 == f3 && f2 == form
verify_mp _ _ _ = False

------------------------------------------------------------------------------------------------------------------------
-- @argument Formula represents the formula on which was applied the uniformal substitution
-- @argument Formula represents the formula proven by applying the uniformal substitution on the first formula
-- @return Bool returns if the rule was applied correctly
verify_usubs :: Formula -> Formula -> Writer [String] Bool
verify_usubs f form = check_substitution $ build_substitution f form

-- @argument Formula represents the formula on which was applied the uniformal substitution
-- @argument Formula represents the formula proven by applying the uniformal substitution on the first formula
-- @return Bool returns a substitution that can be used to obtained the second formula from the first. The substitution 
--              is representing using a list of pair Atom-Formula, meaning atom p should be substituted with formula phi 
--
-- The returned substituion is not necessarily an uniform one and, moreover, if a substitution doesn't exists the 
-- function returns a list containing the element ("", ErrorF)
build_substitution :: Formula -> Formula -> [(Atom, Formula)]
build_substitution F F = []
build_substitution T T = []
build_substitution (AtomF atom) form = [(atom, form)]
build_substitution (NotF f1) (NotF f2) = nub $ build_substitution f1 f2
build_substitution (AndF f1 f2) (AndF f3 f4) = nub $ build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (OrF f1 f2) (OrF f3 f4) = nub $ build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (ImpF f1 f2) (ImpF f3 f4) = nub $ build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (EqvF f1 f2) (EqvF f3 f4) = nub $ build_substitution f1 f3 ++ build_substitution f2 f4
build_substitution (BoxF f1) (BoxF f2) = nub $ build_substitution f1 f2
build_substitution (DiaF f1) (DiaF f2) = nub $ build_substitution f1 f2
build_substitution _ _ = [("", ErrorF)]

-- @argument [(Atom, Formula)] represents a substitution function represented as presented in the above function
-- @return Bool returns if the given substitution doesn't contains errors and if is an uniform substitution
check_substitution :: [(Atom, Formula)] -> Writer [String] Bool
check_substitution subs = 
    let
        has_error = elem ErrorF (map snd subs)
        has_contradictions = 
            let unique_atom_subs = map fst subs
            in nub(unique_atom_subs) /= unique_atom_subs
    in
        if has_error 
        then writer (False, [reason_no_substitution])
        else
            if has_contradictions
            then writer (False, [reason_no_uniform_substitution])
            else return True

------------------------------------------------------------------------------------------------------------------------
-- @argument Formula represents the formula on which it was applied the generalization rule
-- @argument Formula represents the current formula that was proven using the generalization rule applied on the first 
--                   formula
-- @return Bool check if the current formula was obtained by the generalization formula
verify_gen :: Formula -> Formula -> Bool
verify_gen f form = (BoxF f) == form

------------------------------------------------------------------------------------------------------------------------



------------------------------------------------------------------------------------------------------------------------
------------------------------------------------ Other useful functions ------------------------------------------------

-- @argument [(Atom, Formula)] represents an uniform substitution function represented as presented in the above 
--                             functions
-- @argument Formula represents a formula from the modal logic
-- @return Formula returns the formula obtained by applying the uniform substitution on the given formula
make_substitution :: [(Atom, Formula)] -> Formula -> Formula
make_substitution subs F = F
make_substitution subs T = T
make_substitution subs (AtomF atom) = snd.head $ filter (\(at, _) -> at == atom) subs
make_substitution subs (AndF f1 f2) = let 
                                        subs_f1 = make_substitution subs f1
                                        subs_f2 = make_substitution subs f2
                                    in
                                        AndF subs_f1 subs_f2
make_substitution subs (OrF f1 f2) = let 
                                        subs_f1 = make_substitution subs f1
                                        subs_f2 = make_substitution subs f2
                                    in
                                        OrF subs_f1 subs_f2
make_substitution subs (ImpF f1 f2) = let 
                                        subs_f1 = make_substitution subs f1
                                        subs_f2 = make_substitution subs f2
                                    in
                                        ImpF subs_f1 subs_f2
make_substitution subs (EqvF f1 f2) = let 
                                        subs_f1 = make_substitution subs f1
                                        subs_f2 = make_substitution subs f2
                                    in
                                        EqvF subs_f1 subs_f2
make_substitution subs (BoxF f1) = BoxF (make_substitution subs f1)
make_substitution subs (DiaF f1) = DiaF (make_substitution subs f1)