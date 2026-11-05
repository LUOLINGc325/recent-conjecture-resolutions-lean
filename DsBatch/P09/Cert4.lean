import DsBatch.P09.CertData

/-! # P09 — computational certificate (kernels) -/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **Kernel check 1**: every 4-element set of edge indices is avoided by one of
the 55 certificate sets. -/
theorem check4 : go chk 27 0 4 ∅ = true := by
  decide

end DsBatch.P09
