import LazyThinking
open LazyThinking
-- Expected failure: remove the automatic transport theorem, keep other facts fixed.
set_option trace.LazyThinking.Search true in
example : SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search_no_transport using [minimumSplit_contract, minimumSplit_separated, concatenate_guarded_contract]
