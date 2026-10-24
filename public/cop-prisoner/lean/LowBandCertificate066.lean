import LowBandObjective066Transfer
import LowBandObjective066Delivery0
import LowBandObjective066Delivery1
import LowBandObjective066Delivery2
import LowBandObjective066Delivery3
import LowBandObjective066Delivery4
import LowBandObjective066Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate066
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern066.pattern := by
  constructor
  · exact ⟨LowBandObjective066Transfer.data, LowBandObjective066Transfer.checked, LowBandObjective066Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective066Delivery0.data, LowBandObjective066Delivery0.checked, LowBandObjective066Delivery0.initial_states⟩
    · exact ⟨LowBandObjective066Delivery1.data, LowBandObjective066Delivery1.checked, LowBandObjective066Delivery1.initial_states⟩
    · exact ⟨LowBandObjective066Delivery2.data, LowBandObjective066Delivery2.checked, LowBandObjective066Delivery2.initial_states⟩
    · exact ⟨LowBandObjective066Delivery3.data, LowBandObjective066Delivery3.checked, LowBandObjective066Delivery3.initial_states⟩
    · exact ⟨LowBandObjective066Delivery4.data, LowBandObjective066Delivery4.checked, LowBandObjective066Delivery4.initial_states⟩
    · exact ⟨LowBandObjective066Delivery5.data, LowBandObjective066Delivery5.checked, LowBandObjective066Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate066
