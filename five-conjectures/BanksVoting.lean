import Std

/-!
A self-contained certificate for the eight-candidate Banks-tree election.
Each integer score counts agendas, by conditioning on the first retained candidate.
The accompanying proof explains the equal-multiplicity factor in `agendaCount`.
-/

namespace BanksVoting

inductive Candidate where
  | A | B | C | D | E | F | G | H
deriving DecidableEq, BEq, Repr

open Candidate
abbrev Ballot := List Candidate
abbrev Profile := List Ballot

def candidates : List Candidate := [A, B, C, D, E, F, G, H]

def ballotTwo : Ballot := [G, F, D, E, H, B, A, C]
def ballotThree : Ballot := [A, C, D, E, G, B, H, F]
def before : Profile := [[B, H, C, F, E, A, D, G], ballotTwo, ballotThree]
def after : Profile := [[B, H, C, F, E, D, A, G], ballotTwo, ballotThree]

def beats (profile : Profile) (x y : Candidate) : Bool :=
  decide (2 * (profile.filter (fun ballot => ballot.idxOf x < ballot.idxOf y)).length >
    profile.length)

def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k

/-- Count winning agendas for a target among a given list of remaining candidates.
The fuel is initially the number of candidates and drops along with the list.
-/
def agendaCount (profile : Profile) (target : Candidate) :
    Nat → List Candidate → Nat
  | 0, _ => 0
  | fuel + 1, pool => (pool.map fun pivot =>
      let challengers := pool.filter (fun x => beats profile x pivot)
      let tails := fact (pool.length - 1)
      if challengers.isEmpty then
        if pivot == target then tails else 0
      else
        (tails / fact challengers.length) * agendaCount profile target fuel challengers).sum

def score (profile : Profile) (c : Candidate) : Nat :=
  agendaCount profile c candidates.length candidates

/-- Each candidate occurs exactly once in every submitted ballot. -/
def valid (profile : Profile) : Bool :=
  profile.all (fun ballot =>
    ballot.length == candidates.length && candidates.all (fun c => ballot.count c == 1))

theorem valid_profiles : valid before = true ∧ valid after = true := by decide

def only_one_edge_flipped : Bool :=
  candidates.all fun x => candidates.all fun y =>
    if x == D && y == A then !(beats before x y) && beats after x y
    else if x == A && y == D then beats before x y && !(beats after x y)
    else beats before x y == beats after x y

theorem reversal_check : only_one_edge_flipped = true := by decide

theorem before_counts :
    candidates.map (score before) = [4200, 7560, 9240, 10080, 3780, 2940, 2520, 0] := by
  set_option maxRecDepth 100000 in decide

theorem after_counts :
    candidates.map (score after) = [1260, 7308, 13860, 13356, 0, 2016, 2520, 0] := by
  set_option maxRecDepth 100000 in decide

def uniquelyWins (profile : Profile) (winner : Candidate) : Bool :=
  candidates.all fun opponent => opponent == winner || score profile opponent < score profile winner

theorem winner_switch :
    uniquelyWins before D = true ∧ uniquelyWins after C = true ∧
    score before D < score after D := by
  set_option maxRecDepth 100000 in decide


/--
Given a fixed suffix, group remaining candidate labels x by the outcome of the
Banks subtree on (x, suffix). A pair carries that outcome and its multiplicity.
When the next fixed label has subtree outcome p, a label with outcome x gets
the new outcome duel(x,p), exactly the defining two-child Banks recurrence.
Classes defeating p persist. All remaining labels coalesce into the class of p
after removing the chosen label. No probabilities or division enter this count.
-/
abbrev Classes := List (Candidate × Nat)

def childClasses (profile : Profile) (remaining : Nat) (groups : Classes)
    (picked : Candidate) : Classes :=
  let survivors := groups.filter fun group => beats profile group.1 picked
  let mergedSize := remaining - 1 - (survivors.map Prod.snd).sum
  if mergedSize == 0 then survivors else (picked, mergedSize) :: survivors

def treeCount (profile : Profile) (target : Candidate) : Nat → Classes → Nat
  | 0, _ => 0
  | k + 1, groups =>
      match groups with
      | [] => 0
      | first :: rest =>
          if rest.isEmpty then
            if first.1 == target then fact (k + 1) else 0
          else
            (groups.map fun group =>
              group.2 * treeCount profile target k (childClasses profile (k + 1) groups group.1)).sum

def treeScores (profile : Profile) : List Nat :=
  let leaves := candidates.map fun c => (c, 1)
  candidates.map fun target => treeCount profile target candidates.length leaves

theorem binary_tree_before : treeScores before = [4200, 7560, 9240, 10080, 3780, 2940, 2520, 0] := by
  set_option maxRecDepth 100000 in decide

theorem binary_tree_after : treeScores after = [1260, 7308, 13860, 13356, 0, 2016, 2520, 0] := by
  set_option maxRecDepth 100000 in decide

#print axioms binary_tree_before
#print axioms binary_tree_after
#print axioms valid_profiles
#print axioms reversal_check
#print axioms before_counts
#print axioms after_counts
#print axioms winner_switch

end BanksVoting
