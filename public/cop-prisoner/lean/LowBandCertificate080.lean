import LowBandObjective080Transfer
import LowBandObjective080Delivery0
import LowBandObjective080Delivery1
import LowBandObjective080Delivery2
import LowBandObjective080Delivery3
import LowBandObjective080Delivery4
import LowBandObjective080Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate080
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern080.pattern := by
  constructor
  · exact ⟨LowBandObjective080Transfer.data, LowBandObjective080Transfer.checked, LowBandObjective080Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective080Delivery0.data, LowBandObjective080Delivery0.checked, LowBandObjective080Delivery0.initial_states⟩
    · exact ⟨LowBandObjective080Delivery1.data, LowBandObjective080Delivery1.checked, LowBandObjective080Delivery1.initial_states⟩
    · exact ⟨LowBandObjective080Delivery2.data, LowBandObjective080Delivery2.checked, LowBandObjective080Delivery2.initial_states⟩
    · exact ⟨LowBandObjective080Delivery3.data, LowBandObjective080Delivery3.checked, LowBandObjective080Delivery3.initial_states⟩
    · exact ⟨LowBandObjective080Delivery4.data, LowBandObjective080Delivery4.checked, LowBandObjective080Delivery4.initial_states⟩
    · exact ⟨LowBandObjective080Delivery5.data, LowBandObjective080Delivery5.checked, LowBandObjective080Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate080
