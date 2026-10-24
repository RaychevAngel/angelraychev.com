import LowBandObjective070Transfer
import LowBandObjective070Delivery0
import LowBandObjective070Delivery1
import LowBandObjective070Delivery2
import LowBandObjective070Delivery3
import LowBandObjective070Delivery4
import LowBandObjective070Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate070
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern070.pattern := by
  constructor
  · exact ⟨LowBandObjective070Transfer.data, LowBandObjective070Transfer.checked, LowBandObjective070Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective070Delivery0.data, LowBandObjective070Delivery0.checked, LowBandObjective070Delivery0.initial_states⟩
    · exact ⟨LowBandObjective070Delivery1.data, LowBandObjective070Delivery1.checked, LowBandObjective070Delivery1.initial_states⟩
    · exact ⟨LowBandObjective070Delivery2.data, LowBandObjective070Delivery2.checked, LowBandObjective070Delivery2.initial_states⟩
    · exact ⟨LowBandObjective070Delivery3.data, LowBandObjective070Delivery3.checked, LowBandObjective070Delivery3.initial_states⟩
    · exact ⟨LowBandObjective070Delivery4.data, LowBandObjective070Delivery4.checked, LowBandObjective070Delivery4.initial_states⟩
    · exact ⟨LowBandObjective070Delivery5.data, LowBandObjective070Delivery5.checked, LowBandObjective070Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate070
