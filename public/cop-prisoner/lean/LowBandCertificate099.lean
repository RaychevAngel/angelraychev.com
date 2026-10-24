import LowBandObjective099Transfer
import LowBandObjective099Delivery0
import LowBandObjective099Delivery1
import LowBandObjective099Delivery2
import LowBandObjective099Delivery3
import LowBandObjective099Delivery4
import LowBandObjective099Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate099
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern099.pattern := by
  constructor
  · exact ⟨LowBandObjective099Transfer.data, LowBandObjective099Transfer.checked, LowBandObjective099Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective099Delivery0.data, LowBandObjective099Delivery0.checked, LowBandObjective099Delivery0.initial_states⟩
    · exact ⟨LowBandObjective099Delivery1.data, LowBandObjective099Delivery1.checked, LowBandObjective099Delivery1.initial_states⟩
    · exact ⟨LowBandObjective099Delivery2.data, LowBandObjective099Delivery2.checked, LowBandObjective099Delivery2.initial_states⟩
    · exact ⟨LowBandObjective099Delivery3.data, LowBandObjective099Delivery3.checked, LowBandObjective099Delivery3.initial_states⟩
    · exact ⟨LowBandObjective099Delivery4.data, LowBandObjective099Delivery4.checked, LowBandObjective099Delivery4.initial_states⟩
    · exact ⟨LowBandObjective099Delivery5.data, LowBandObjective099Delivery5.checked, LowBandObjective099Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate099
