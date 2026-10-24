import LowBandObjective047Transfer
import LowBandObjective047Delivery0
import LowBandObjective047Delivery1
import LowBandObjective047Delivery2
import LowBandObjective047Delivery3
import LowBandObjective047Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate047
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern047.pattern := by
  constructor
  · exact ⟨LowBandObjective047Transfer.data, LowBandObjective047Transfer.checked, LowBandObjective047Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective047Delivery0.data, LowBandObjective047Delivery0.checked, LowBandObjective047Delivery0.initial_states⟩
    · exact ⟨LowBandObjective047Delivery1.data, LowBandObjective047Delivery1.checked, LowBandObjective047Delivery1.initial_states⟩
    · exact ⟨LowBandObjective047Delivery2.data, LowBandObjective047Delivery2.checked, LowBandObjective047Delivery2.initial_states⟩
    · exact ⟨LowBandObjective047Delivery3.data, LowBandObjective047Delivery3.checked, LowBandObjective047Delivery3.initial_states⟩
    · simp [LowBandPattern047.pattern] at present
    · exact ⟨LowBandObjective047Delivery5.data, LowBandObjective047Delivery5.checked, LowBandObjective047Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate047
