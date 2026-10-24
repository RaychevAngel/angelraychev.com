import LowBandObjective065Transfer
import LowBandObjective065Delivery0
import LowBandObjective065Delivery1
import LowBandObjective065Delivery2
import LowBandObjective065Delivery3
import LowBandObjective065Delivery4
import LowBandObjective065Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate065
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern065.pattern := by
  constructor
  · exact ⟨LowBandObjective065Transfer.data, LowBandObjective065Transfer.checked, LowBandObjective065Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective065Delivery0.data, LowBandObjective065Delivery0.checked, LowBandObjective065Delivery0.initial_states⟩
    · exact ⟨LowBandObjective065Delivery1.data, LowBandObjective065Delivery1.checked, LowBandObjective065Delivery1.initial_states⟩
    · exact ⟨LowBandObjective065Delivery2.data, LowBandObjective065Delivery2.checked, LowBandObjective065Delivery2.initial_states⟩
    · exact ⟨LowBandObjective065Delivery3.data, LowBandObjective065Delivery3.checked, LowBandObjective065Delivery3.initial_states⟩
    · exact ⟨LowBandObjective065Delivery4.data, LowBandObjective065Delivery4.checked, LowBandObjective065Delivery4.initial_states⟩
    · exact ⟨LowBandObjective065Delivery5.data, LowBandObjective065Delivery5.checked, LowBandObjective065Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate065
