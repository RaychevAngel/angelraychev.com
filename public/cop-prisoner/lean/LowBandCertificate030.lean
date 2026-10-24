import LowBandObjective030Transfer
import LowBandObjective030Delivery0
import LowBandObjective030Delivery1
import LowBandObjective030Delivery2
import LowBandObjective030Delivery3
import LowBandObjective030Delivery4
import LowBandObjective030Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate030
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern030.pattern := by
  constructor
  · exact ⟨LowBandObjective030Transfer.data, LowBandObjective030Transfer.checked, LowBandObjective030Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective030Delivery0.data, LowBandObjective030Delivery0.checked, LowBandObjective030Delivery0.initial_states⟩
    · exact ⟨LowBandObjective030Delivery1.data, LowBandObjective030Delivery1.checked, LowBandObjective030Delivery1.initial_states⟩
    · exact ⟨LowBandObjective030Delivery2.data, LowBandObjective030Delivery2.checked, LowBandObjective030Delivery2.initial_states⟩
    · exact ⟨LowBandObjective030Delivery3.data, LowBandObjective030Delivery3.checked, LowBandObjective030Delivery3.initial_states⟩
    · exact ⟨LowBandObjective030Delivery4.data, LowBandObjective030Delivery4.checked, LowBandObjective030Delivery4.initial_states⟩
    · exact ⟨LowBandObjective030Delivery5.data, LowBandObjective030Delivery5.checked, LowBandObjective030Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate030
