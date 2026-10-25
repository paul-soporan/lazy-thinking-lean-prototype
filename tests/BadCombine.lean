import LazyThinking
open LazyThinking
-- Expected failure: the half split does not establish separation on all inputs.
set_option trace.LazyThinking.Search true in
example : SchemeRequirements leftHalf rightHalf concatenate := by
  lazy_search using [halfSplit_contract, concatenate_guarded_contract]
