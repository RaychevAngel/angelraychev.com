import LowBandObjective069Transfer
import LowBandObjective069Delivery0
import LowBandObjective069Delivery1
import LowBandObjective069Delivery2
import LowBandObjective069Delivery3
import LowBandObjective069Delivery4
import LowBandObjective069Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate069
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern069.pattern := by
  constructor
  · exact ⟨LowBandObjective069Transfer.data, LowBandObjective069Transfer.checked, LowBandObjective069Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective069Delivery0.data, LowBandObjective069Delivery0.checked, LowBandObjective069Delivery0.initial_states⟩
    · exact ⟨LowBandObjective069Delivery1.data, LowBandObjective069Delivery1.checked, LowBandObjective069Delivery1.initial_states⟩
    · exact ⟨LowBandObjective069Delivery2.data, LowBandObjective069Delivery2.checked, LowBandObjective069Delivery2.initial_states⟩
    · exact ⟨LowBandObjective069Delivery3.data, LowBandObjective069Delivery3.checked, LowBandObjective069Delivery3.initial_states⟩
    · exact ⟨LowBandObjective069Delivery4.data, LowBandObjective069Delivery4.checked, LowBandObjective069Delivery4.initial_states⟩
    · exact ⟨LowBandObjective069Delivery5.data, LowBandObjective069Delivery5.checked, LowBandObjective069Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate069
