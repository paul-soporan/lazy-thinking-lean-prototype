import LazyThinking
import LazyThinking.Diagnostics
open LazyThinking
-- Contents and separation are both proved, but the uniform-input split cannot decrease.
set_option trace.LazyThinking.Search true in
example : SchemeRequirements rawMinimumLeft rawMinimumRight concatenate := by
  lazy_search using [rawMinimum_contents, rawMinimum_separated, concatenate_guarded_contract]
