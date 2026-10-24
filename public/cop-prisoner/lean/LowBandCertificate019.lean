import LowBandObjective019Transfer
import LowBandObjective019Delivery0
import LowBandObjective019Delivery1
import LowBandObjective019Delivery2
import LowBandObjective019Delivery3
import LowBandObjective019Delivery4
import LowBandObjective019Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate019
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern019.pattern := by
  constructor
  · exact ⟨LowBandObjective019Transfer.data, LowBandObjective019Transfer.checked, LowBandObjective019Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective019Delivery0.data, LowBandObjective019Delivery0.checked, LowBandObjective019Delivery0.initial_states⟩
    · exact ⟨LowBandObjective019Delivery1.data, LowBandObjective019Delivery1.checked, LowBandObjective019Delivery1.initial_states⟩
    · exact ⟨LowBandObjective019Delivery2.data, LowBandObjective019Delivery2.checked, LowBandObjective019Delivery2.initial_states⟩
    · exact ⟨LowBandObjective019Delivery3.data, LowBandObjective019Delivery3.checked, LowBandObjective019Delivery3.initial_states⟩
    · exact ⟨LowBandObjective019Delivery4.data, LowBandObjective019Delivery4.checked, LowBandObjective019Delivery4.initial_states⟩
    · exact ⟨LowBandObjective019Delivery5.data, LowBandObjective019Delivery5.checked, LowBandObjective019Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate019
