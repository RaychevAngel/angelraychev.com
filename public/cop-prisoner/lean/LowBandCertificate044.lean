import LowBandObjective044Transfer
import LowBandObjective044Delivery0
import LowBandObjective044Delivery1
import LowBandObjective044Delivery2
import LowBandObjective044Delivery3
import LowBandObjective044Delivery4
import LowBandObjective044Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate044
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern044.pattern := by
  constructor
  · exact ⟨LowBandObjective044Transfer.data, LowBandObjective044Transfer.checked, LowBandObjective044Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective044Delivery0.data, LowBandObjective044Delivery0.checked, LowBandObjective044Delivery0.initial_states⟩
    · exact ⟨LowBandObjective044Delivery1.data, LowBandObjective044Delivery1.checked, LowBandObjective044Delivery1.initial_states⟩
    · exact ⟨LowBandObjective044Delivery2.data, LowBandObjective044Delivery2.checked, LowBandObjective044Delivery2.initial_states⟩
    · exact ⟨LowBandObjective044Delivery3.data, LowBandObjective044Delivery3.checked, LowBandObjective044Delivery3.initial_states⟩
    · exact ⟨LowBandObjective044Delivery4.data, LowBandObjective044Delivery4.checked, LowBandObjective044Delivery4.initial_states⟩
    · exact ⟨LowBandObjective044Delivery5.data, LowBandObjective044Delivery5.checked, LowBandObjective044Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate044
