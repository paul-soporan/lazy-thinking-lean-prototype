import LazyThinking
open LazyThinking
-- Expected failure with the same witnesses as the successful adaptive search.
set_option trace.LazyThinking true in
example : SchemeRequirements minimumLeft minimumRight concatenate := by
  lazy_thinking using [minimumSplit_contract, minimumSplit_separated, concatenate_guarded_contract]
