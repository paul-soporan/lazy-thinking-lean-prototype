import LazyThinking
open LazyThinking

def main : IO Unit := do
  IO.println "Lazy thinking in Lean — checked list-sorting experiments"
  for xs in [[], [7], [2, 1], [3, 1, 3, 2], [5, 2, 4, 1, 6, 3, 2]] do
    IO.println s!"{xs} → merge: {mergeSort xs}; minimum-partition: {minimumPartitionSort xs}"
