import LazyThinking
open LazyThinking
-- Deliberately false postulate, isolated to an expected-failure fixture.
axiom bogusCombine : CombineContract concatenate
set_option trace.LazyThinking.Search true in
example : SchemeRequirements leftHalf rightHalf concatenate := by
  lazy_search using [halfSplit_contract, bogusCombine]
