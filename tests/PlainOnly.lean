import LazyThinking
open LazyThinking
-- Expected failure: the finite candidate menu is reduced to the unguarded pattern.
set_option trace.LazyThinking.Search true in
example : SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_search_plain using [minimumSplit_contract, minimumSplit_separated, concatenate_guarded_contract]
