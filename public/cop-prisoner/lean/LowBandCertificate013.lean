import LowBandObjective013Transfer
import LowBandObjective013Delivery0
import LowBandObjective013Delivery1
import LowBandObjective013Delivery2
import LowBandObjective013Delivery3
import LowBandObjective013Delivery4
import LowBandObjective013Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate013
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern013.pattern := by
  constructor
  · exact ⟨LowBandObjective013Transfer.data, LowBandObjective013Transfer.checked, LowBandObjective013Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective013Delivery0.data, LowBandObjective013Delivery0.checked, LowBandObjective013Delivery0.initial_states⟩
    · exact ⟨LowBandObjective013Delivery1.data, LowBandObjective013Delivery1.checked, LowBandObjective013Delivery1.initial_states⟩
    · exact ⟨LowBandObjective013Delivery2.data, LowBandObjective013Delivery2.checked, LowBandObjective013Delivery2.initial_states⟩
    · exact ⟨LowBandObjective013Delivery3.data, LowBandObjective013Delivery3.checked, LowBandObjective013Delivery3.initial_states⟩
    · exact ⟨LowBandObjective013Delivery4.data, LowBandObjective013Delivery4.checked, LowBandObjective013Delivery4.initial_states⟩
    · exact ⟨LowBandObjective013Delivery5.data, LowBandObjective013Delivery5.checked, LowBandObjective013Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate013
