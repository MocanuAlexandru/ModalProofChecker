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

data Model = Model [World] Relation LabelFunction

data Frame = Frame [World] Relation

valid_frame :: Frame -> Formula -> Bool
valid_frame = undefined --should check all labeling functions
