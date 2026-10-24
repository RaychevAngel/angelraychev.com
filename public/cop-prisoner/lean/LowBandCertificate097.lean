import LowBandObjective097Transfer
import LowBandObjective097Delivery0
import LowBandObjective097Delivery1
import LowBandObjective097Delivery2
import LowBandObjective097Delivery3
import LowBandObjective097Delivery4
import LowBandObjective097Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate097
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern097.pattern := by
  constructor
  · exact ⟨LowBandObjective097Transfer.data, LowBandObjective097Transfer.checked, LowBandObjective097Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective097Delivery0.data, LowBandObjective097Delivery0.checked, LowBandObjective097Delivery0.initial_states⟩
    · exact ⟨LowBandObjective097Delivery1.data, LowBandObjective097Delivery1.checked, LowBandObjective097Delivery1.initial_states⟩
    · exact ⟨LowBandObjective097Delivery2.data, LowBandObjective097Delivery2.checked, LowBandObjective097Delivery2.initial_states⟩
    · exact ⟨LowBandObjective097Delivery3.data, LowBandObjective097Delivery3.checked, LowBandObjective097Delivery3.initial_states⟩
    · exact ⟨LowBandObjective097Delivery4.data, LowBandObjective097Delivery4.checked, LowBandObjective097Delivery4.initial_states⟩
    · exact ⟨LowBandObjective097Delivery5.data, LowBandObjective097Delivery5.checked, LowBandObjective097Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate097
