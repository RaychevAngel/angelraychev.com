import LowBandObjective094Transfer
import LowBandObjective094Delivery0
import LowBandObjective094Delivery1
import LowBandObjective094Delivery2
import LowBandObjective094Delivery3
import LowBandObjective094Delivery4
import LowBandObjective094Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate094
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern094.pattern := by
  constructor
  · exact ⟨LowBandObjective094Transfer.data, LowBandObjective094Transfer.checked, LowBandObjective094Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective094Delivery0.data, LowBandObjective094Delivery0.checked, LowBandObjective094Delivery0.initial_states⟩
    · exact ⟨LowBandObjective094Delivery1.data, LowBandObjective094Delivery1.checked, LowBandObjective094Delivery1.initial_states⟩
    · exact ⟨LowBandObjective094Delivery2.data, LowBandObjective094Delivery2.checked, LowBandObjective094Delivery2.initial_states⟩
    · exact ⟨LowBandObjective094Delivery3.data, LowBandObjective094Delivery3.checked, LowBandObjective094Delivery3.initial_states⟩
    · exact ⟨LowBandObjective094Delivery4.data, LowBandObjective094Delivery4.checked, LowBandObjective094Delivery4.initial_states⟩
    · exact ⟨LowBandObjective094Delivery5.data, LowBandObjective094Delivery5.checked, LowBandObjective094Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate094
