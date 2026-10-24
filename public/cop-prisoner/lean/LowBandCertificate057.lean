import LowBandObjective057Transfer
import LowBandObjective057Delivery0
import LowBandObjective057Delivery1
import LowBandObjective057Delivery2
import LowBandObjective057Delivery3
import LowBandObjective057Delivery4
import LowBandObjective057Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate057
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern057.pattern := by
  constructor
  · exact ⟨LowBandObjective057Transfer.data, LowBandObjective057Transfer.checked, LowBandObjective057Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective057Delivery0.data, LowBandObjective057Delivery0.checked, LowBandObjective057Delivery0.initial_states⟩
    · exact ⟨LowBandObjective057Delivery1.data, LowBandObjective057Delivery1.checked, LowBandObjective057Delivery1.initial_states⟩
    · exact ⟨LowBandObjective057Delivery2.data, LowBandObjective057Delivery2.checked, LowBandObjective057Delivery2.initial_states⟩
    · exact ⟨LowBandObjective057Delivery3.data, LowBandObjective057Delivery3.checked, LowBandObjective057Delivery3.initial_states⟩
    · exact ⟨LowBandObjective057Delivery4.data, LowBandObjective057Delivery4.checked, LowBandObjective057Delivery4.initial_states⟩
    · exact ⟨LowBandObjective057Delivery5.data, LowBandObjective057Delivery5.checked, LowBandObjective057Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate057
