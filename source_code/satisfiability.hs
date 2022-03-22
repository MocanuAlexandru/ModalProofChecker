import Data.Bool

type Atom = String
data Formula = F | T 
               | AtomF Atom
               | NotF Formula 
               | AndF Formula Formula
               | OrF Formula Formula
               | ImpF Formula Formula
               | EqvF Formula Formula
               | SquF Formula
               | DiaF Formula
               deriving(Show, Eq)

type World = String
type Relation = [(World,World)]
type LabelFunction = [(World, [Atom])]

data Model = Model {
    get_worlds :: [World],
    get_relation :: Relation,
    get_labelFun :: LabelFunction
    }

get_true_atoms :: LabelFunction -> World -> [Atom]
get_true_atoms l w = 
    snd $ (filter (\(y, _) -> if w==y then True else False) l) !! 0

get_next_worlds :: Relation -> World -> [World]
get_next_worlds r w = map snd $
    filter (\(y, _) -> if w==y then True else False) r

satisfy_world_atomic :: Model -> World -> Atom -> Bool
satisfy_world_atomic model w atom = 
    elem atom $ get_true_atoms (get_labelFun model) w

satisfy_world :: Model -> World -> Formula -> Bool
satisfy_world _ _ T = True
satisfy_world _ _ F = False
satisfy_world model w (AtomF atom) = satisfy_world_atomic model w atom
satisfy_world model w (NotF form) = not (satisfy_world model w form)
satisfy_world model w (AndF formL formR) = 
    (satisfy_world model w formL) && (satisfy_world model w formR)
satisfy_world model w (OrF formL formR) = 
    (satisfy_world model w formL) || (satisfy_world model w formR)
satisfy_world model w (ImpF formL formR) = 
    if (satisfy_world model w formL) 
    then (satisfy_world model w formR) 
    else True
satisfy_world model w (EqvF formL formR) = 
    (satisfy_world model w formL) == (satisfy_world model w formR)
satisfy_world model w (SquF form) = 
    and [satisfy_world model wprim form | 
         wprim <- get_next_worlds (get_relation model) w]
satisfy_world model w (DiaF form) = 
    or [satisfy_world model wprim form | 
        wprim <- get_next_worlds (get_relation model) w]

satisfy_model :: Model -> Formula -> Bool
satisfy_model model form = 
    and [satisfy_world model w form | w <- (get_worlds model)]

satisfy_forms_world :: Model -> World -> [Formula] -> Formula -> Bool
satisfy_forms_world model w forms form = 
    if and [satisfy_world model w formPrim | formPrim <- forms]
    then satisfy_world model w form
    else True

satisfy_forms :: Model -> [Formula] -> Formula -> Bool
satisfy_forms model forms form = 
    and [satisfy_forms_world model w forms form | w <- (get_worlds model)]

valid :: Formula -> Bool
valid form = undefined --form should be true in every world of every model

