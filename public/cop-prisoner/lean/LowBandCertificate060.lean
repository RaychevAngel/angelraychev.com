import LowBandObjective060Transfer
import LowBandObjective060Delivery0
import LowBandObjective060Delivery1
import LowBandObjective060Delivery2
import LowBandObjective060Delivery3
import LowBandObjective060Delivery4
import LowBandObjective060Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate060
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern060.pattern := by
  constructor
  · exact ⟨LowBandObjective060Transfer.data, LowBandObjective060Transfer.checked, LowBandObjective060Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective060Delivery0.data, LowBandObjective060Delivery0.checked, LowBandObjective060Delivery0.initial_states⟩
    · exact ⟨LowBandObjective060Delivery1.data, LowBandObjective060Delivery1.checked, LowBandObjective060Delivery1.initial_states⟩
    · exact ⟨LowBandObjective060Delivery2.data, LowBandObjective060Delivery2.checked, LowBandObjective060Delivery2.initial_states⟩
    · exact ⟨LowBandObjective060Delivery3.data, LowBandObjective060Delivery3.checked, LowBandObjective060Delivery3.initial_states⟩
    · exact ⟨LowBandObjective060Delivery4.data, LowBandObjective060Delivery4.checked, LowBandObjective060Delivery4.initial_states⟩
    · exact ⟨LowBandObjective060Delivery5.data, LowBandObjective060Delivery5.checked, LowBandObjective060Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate060
