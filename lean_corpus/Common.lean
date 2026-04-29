/-
Shared imports and openings for every chapter file in this corpus.
Each PN.lean does `import LeanCorpus.Common` and lives in `namespace AITP.PN`.
-/
import Mathlib
import Aesop

set_option maxHeartbeats 400000

open BigOperators Real Nat Topology Function MeasureTheory intervalIntegral Set Finset Complex
