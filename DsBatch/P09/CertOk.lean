import DsBatch.P09.CertData

/-! # P09 — computational certificate (kernels) -/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **Kernel check 3**: all 55 certificates are correct: `D` dominates `G`, each
bundled vertex lies outside `D` and has its edge list recorded exactly, and
every vertex outside `D` is bundled. -/
theorem certs_ok : certs.all certOk = true := by
  decide

end DsBatch.P09
