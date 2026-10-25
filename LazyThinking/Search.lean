import LazyThinking.Tactic
import LazyThinking.Candidates

/-!
A finite search over two supplied contract patterns. Candidate generation,
premise discharge, and acceptance are distinct. Failure to prove a candidate's
premises is recorded as unresolved, never as mathematical impossibility.
-/

namespace LazyThinking
open Lean Meta Elab Tactic

initialize registerTraceClass `LazyThinking.Search

structure SearchEvent where
  stage : String
  candidate : String
  detail : String
  goals : Array String
  deriving ToJson

private def propose (candidate : ContractCandidate) (jointOnly : Bool) : TacticM Unit := do
  match candidate, jointOnly with
  | .unconditional, true => evalTactic (← `(tactic| apply joint_of_contracts))
  | .unconditional, false => evalTactic (← `(tactic| apply scheme_of_contracts))
  | .separated, true =>
      evalTactic (← `(tactic| apply joint_of_guarded_contracts (guard := Separated)))
  | .separated, false =>
      evalTactic (← `(tactic| apply scheme_of_guarded_contracts (guard := Separated)))

private def runSearch (candidates : Array ContractCandidate)
    (useTransport : Bool) (facts : Array (TSyntax `term)) : TacticM Unit := do
  if (← getGoals).length != 1 then throwError "lazy_search expects one focused goal"
  withMainContext do
    let originalGoal ← getMainGoal
    let head := (← instantiateMVars (← getMainTarget)).getAppFn.constName?
    if head != some ``SchemeRequirements && head != some ``JointRequirement then
      throwError "lazy_search supports SchemeRequirements and JointRequirement goals"
    let initialGoals ← Evidence.snapshot
    let direct ← Evidence.tryProof originalGoal (← `(tactic| assumption))
    if direct then
      let event : SearchEvent := ⟨"complete", "direct", "Existing local proof.", #[]⟩
      trace[LazyThinking.Search] "{(toJson event).compress}"
      return
    let base ← saveState
    let mut events : Array SearchEvent := #[
      ⟨"attempt", "", "Start finite candidate search.", initialGoals⟩]
    let mut best : Option (Lean.Elab.Tactic.SavedState × Nat × String) := none
    let mut complete := false
    for candidate in candidates do
      if !complete then
        base.restore
        propose candidate (head == some ``JointRequirement)
        events := events.push ⟨"candidate", candidate.label,
          "Generated obligations; no premise is assumed true.", ← Evidence.snapshot⟩
        let mut available := facts
        if useTransport && candidate == .separated then
          available := available.push (← `(term| separation_transport))
        Evidence.discharge available
        let residual ← Evidence.snapshot
        let count := (← getGoals).length
        if count == 0 then
          Evidence.checkProofDependencies originalGoal
          complete := true
          best := some (← saveState, 0, candidate.label)
          events := events.push ⟨"selected", candidate.label,
            "All candidate premises discharged; checked proof constructed.", residual⟩
        else
          events := events.push ⟨"candidate_unresolved", candidate.label,
            "Unproved premises; this is not a refutation of the candidate.", residual⟩
          let improves := match best with
            | none => true
            | some (_, cost, _) => count < cost
          if improves then
            best := some (← saveState, count, candidate.label)
    match best with
    | some (state, _, label) =>
      state.restore
      events := events.push ⟨if complete then "complete" else "unresolved", label,
        if complete then "The goal has a checked proof."
        else "Search exhausted; retain the candidate with fewest open premises.",
        ← Evidence.snapshot⟩
    | none =>
      base.restore
      events := events.push ⟨"unresolved", "", "No candidate was available.", initialGoals⟩
    -- Emit after restoring the chosen state so backtracking does not erase reports.
    for event in events do
      trace[LazyThinking.Search] "{(toJson event).compress}"

syntax "lazy_search" : tactic
syntax "lazy_search" " using " "[" term,* "]" : tactic
syntax "lazy_search_plain" " using " "[" term,* "]" : tactic
syntax "lazy_search_no_transport" " using " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| lazy_search) => runSearch #[.unconditional, .separated] true #[]
  | `(tactic| lazy_search using [$facts,*]) =>
      runSearch #[.unconditional, .separated] true facts.getElems
  | `(tactic| lazy_search_plain using [$facts,*]) =>
      runSearch #[.unconditional] true facts.getElems
  | `(tactic| lazy_search_no_transport using [$facts,*]) =>
      runSearch #[.unconditional, .separated] false facts.getElems

end LazyThinking
