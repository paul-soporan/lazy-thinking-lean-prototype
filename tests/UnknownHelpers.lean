import LazyThinking
open LazyThinking
-- Expected failure: arbitrary helpers have no supplied requirement witnesses.
set_option trace.LazyThinking.Search true in
example (left right : Splitter) (combine : Combiner) :
    SchemeRequirements left right combine := by
  lazy_search
