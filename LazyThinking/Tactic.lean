import LazyThinking.Decomposition
import LazyThinking.Evidence

namespace LazyThinking
open Lean Meta Elab Tactic

initialize registerTraceClass `LazyThinking

structure ThinkingEvent where
  stage : String
  detail : String
  goals : Array String
  deriving ToJson

private def recordEvent (stage detail : String) : TacticM Unit := do
  let event : ThinkingEvent := ⟨stage, detail, ← Evidence.snapshot⟩
  trace[LazyThinking] "{(toJson event).compress}"

private def runLazyThinking (facts : Array (TSyntax `term)) : TacticM Unit := do
  if (← getGoals).length != 1 then
    throwError "lazy_thinking expects one focused goal"
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let head := target.getAppFn.constName?
    if head != some ``JointRequirement && head != some ``SchemeRequirements then
      throwError "lazy_thinking supports JointRequirement and SchemeRequirements goals"
    recordEvent "attempt" "Try assumptions and logical simplification without new requirements."
    let goal ← getMainGoal
    let solved ← Evidence.tryProof goal (← `(tactic| first
      | assumption
      | solve | simp only [SchemeRequirements, JointRequirement, SortSpec]))
    if solved then
      recordEvent "complete" "The initial proof procedure solved the original goal."
    else
      recordEvent "stalled" "The bounded proof attempt did not establish the joint requirement."
      if head == some ``JointRequirement then
        evalTactic (← `(tactic| apply joint_of_contracts))
      else
        evalTactic (← `(tactic| apply scheme_of_contracts))
      recordEvent "requirements" "Apply the supplied concatenation/permutation decomposition rule."
      Evidence.discharge facts
      if (← getGoals).isEmpty then
        recordEvent "complete" "Requirements discharged using local assumptions or supplied witnesses."
      else
        recordEvent "unresolved" "Remaining requirements are Lean goals; the theorem is not proved."

syntax "lazy_thinking" : tactic
syntax "lazy_thinking" " using " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| lazy_thinking) => runLazyThinking #[]
  | `(tactic| lazy_thinking using [$facts,*]) => runLazyThinking facts.getElems

end LazyThinking
