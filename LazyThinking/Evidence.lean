import Lean

namespace LazyThinking.Evidence
open Lean Meta Elab Tactic

def snapshot : TacticM (Array String) := do
  let mut goals := #[]
  for goal in ← getGoals do
    goals := goals.push (← goal.withContext do return (← ppGoal goal).pretty)
  return goals

/-- These are the standard foundations accepted for this experiment. -/
def checkProofDependencies (goal : MVarId) : TacticM Unit := do
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasExprMVar then throwError "proof has unresolved metavariables"
  for name in proof.getUsedConstants do
    for axiomName in ← collectAxioms name do
      if axiomName != ``propext && axiomName != ``Quot.sound &&
          axiomName != ``Classical.choice then
        throwError "rejected proof dependency {axiomName}"

/-- A failed attempt restores assignments, goals, and local proof state. -/
def tryProof (goal : MVarId) (tactic : TSyntax `tactic) : TacticM Bool := do
  let before ← saveState
  try
    withoutRecover <| evalTactic tactic
    unless (← getGoals).isEmpty do
      before.restore
      return false
    checkProofDependencies goal
    return true
  catch _ =>
    before.restore
    return false

def discharge (facts : Array (TSyntax `term)) : TacticM Unit := do
  let goals ← getGoals
  let mut remaining := []
  for goal in goals do
    setGoals [goal]
    let mut solved ← tryProof goal (← `(tactic| assumption))
    for fact in facts do
      if !solved then solved ← tryProof goal (← `(tactic| exact $fact))
    if !solved then remaining := remaining ++ [goal]
  setGoals remaining

end LazyThinking.Evidence
