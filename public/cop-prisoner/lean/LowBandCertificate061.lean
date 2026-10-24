import LowBandObjective061Transfer
import LowBandObjective061Delivery0
import LowBandObjective061Delivery1
import LowBandObjective061Delivery2
import LowBandObjective061Delivery3
import LowBandObjective061Delivery4
import LowBandObjective061Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate061
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern061.pattern := by
  constructor
  · exact ⟨LowBandObjective061Transfer.data, LowBandObjective061Transfer.checked, LowBandObjective061Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective061Delivery0.data, LowBandObjective061Delivery0.checked, LowBandObjective061Delivery0.initial_states⟩
    · exact ⟨LowBandObjective061Delivery1.data, LowBandObjective061Delivery1.checked, LowBandObjective061Delivery1.initial_states⟩
    · exact ⟨LowBandObjective061Delivery2.data, LowBandObjective061Delivery2.checked, LowBandObjective061Delivery2.initial_states⟩
    · exact ⟨LowBandObjective061Delivery3.data, LowBandObjective061Delivery3.checked, LowBandObjective061Delivery3.initial_states⟩
    · exact ⟨LowBandObjective061Delivery4.data, LowBandObjective061Delivery4.checked, LowBandObjective061Delivery4.initial_states⟩
    · exact ⟨LowBandObjective061Delivery5.data, LowBandObjective061Delivery5.checked, LowBandObjective061Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate061
