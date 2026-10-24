import LowBandObjective027Transfer
import LowBandObjective027Delivery0
import LowBandObjective027Delivery1
import LowBandObjective027Delivery2
import LowBandObjective027Delivery3
import LowBandObjective027Delivery4
import LowBandObjective027Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate027
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern027.pattern := by
  constructor
  · exact ⟨LowBandObjective027Transfer.data, LowBandObjective027Transfer.checked, LowBandObjective027Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective027Delivery0.data, LowBandObjective027Delivery0.checked, LowBandObjective027Delivery0.initial_states⟩
    · exact ⟨LowBandObjective027Delivery1.data, LowBandObjective027Delivery1.checked, LowBandObjective027Delivery1.initial_states⟩
    · exact ⟨LowBandObjective027Delivery2.data, LowBandObjective027Delivery2.checked, LowBandObjective027Delivery2.initial_states⟩
    · exact ⟨LowBandObjective027Delivery3.data, LowBandObjective027Delivery3.checked, LowBandObjective027Delivery3.initial_states⟩
    · exact ⟨LowBandObjective027Delivery4.data, LowBandObjective027Delivery4.checked, LowBandObjective027Delivery4.initial_states⟩
    · exact ⟨LowBandObjective027Delivery5.data, LowBandObjective027Delivery5.checked, LowBandObjective027Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate027
