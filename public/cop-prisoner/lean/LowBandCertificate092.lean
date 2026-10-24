import LowBandObjective092Transfer
import LowBandObjective092Delivery0
import LowBandObjective092Delivery1
import LowBandObjective092Delivery2
import LowBandObjective092Delivery3
import LowBandObjective092Delivery4
import LowBandObjective092Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate092
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern092.pattern := by
  constructor
  · exact ⟨LowBandObjective092Transfer.data, LowBandObjective092Transfer.checked, LowBandObjective092Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective092Delivery0.data, LowBandObjective092Delivery0.checked, LowBandObjective092Delivery0.initial_states⟩
    · exact ⟨LowBandObjective092Delivery1.data, LowBandObjective092Delivery1.checked, LowBandObjective092Delivery1.initial_states⟩
    · exact ⟨LowBandObjective092Delivery2.data, LowBandObjective092Delivery2.checked, LowBandObjective092Delivery2.initial_states⟩
    · exact ⟨LowBandObjective092Delivery3.data, LowBandObjective092Delivery3.checked, LowBandObjective092Delivery3.initial_states⟩
    · exact ⟨LowBandObjective092Delivery4.data, LowBandObjective092Delivery4.checked, LowBandObjective092Delivery4.initial_states⟩
    · exact ⟨LowBandObjective092Delivery5.data, LowBandObjective092Delivery5.checked, LowBandObjective092Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate092
