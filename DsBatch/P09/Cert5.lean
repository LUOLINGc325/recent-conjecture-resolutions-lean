import DsBatch.P09.CertData

/-! # P09 — computational certificate (kernels) -/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **Kernel check 2**: no 5-element set of vertices dominates `G`. -/
theorem check5 : go notDomB 18 0 5 ∅ = true := by
  decide

end DsBatch.P09
