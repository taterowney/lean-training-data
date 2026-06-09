module

public section


namespace Array

/-- Deduplicate an array. Worse time complexity than `Array.dedupSorted` i guess (O(n^2) vs O(n log n)) but doesn't require an ordering on `α`. -/
def dedup {α : Type} [BEq α] (arr : Array α) : Array α := Id.run do
  let mut res : Array α := #[]
  for elem in arr do
    unless res.contains elem do
      res := res.push elem
  res

end Array
end
