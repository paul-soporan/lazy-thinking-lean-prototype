import LazyThinking
open LazyThinking
-- Expected failure: the necessary split-guard witness is not supplied.
set_option trace.LazyThinking.Search true in
example : SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search using [minimumSplit_contract, concatenate_guarded_contract]
