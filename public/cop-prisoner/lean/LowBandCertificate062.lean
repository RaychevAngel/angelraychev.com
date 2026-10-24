import LowBandObjective062Transfer
import LowBandObjective062Delivery0
import LowBandObjective062Delivery1
import LowBandObjective062Delivery2
import LowBandObjective062Delivery3
import LowBandObjective062Delivery4
import LowBandObjective062Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate062
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern062.pattern := by
  constructor
  · exact ⟨LowBandObjective062Transfer.data, LowBandObjective062Transfer.checked, LowBandObjective062Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective062Delivery0.data, LowBandObjective062Delivery0.checked, LowBandObjective062Delivery0.initial_states⟩
    · exact ⟨LowBandObjective062Delivery1.data, LowBandObjective062Delivery1.checked, LowBandObjective062Delivery1.initial_states⟩
    · exact ⟨LowBandObjective062Delivery2.data, LowBandObjective062Delivery2.checked, LowBandObjective062Delivery2.initial_states⟩
    · exact ⟨LowBandObjective062Delivery3.data, LowBandObjective062Delivery3.checked, LowBandObjective062Delivery3.initial_states⟩
    · exact ⟨LowBandObjective062Delivery4.data, LowBandObjective062Delivery4.checked, LowBandObjective062Delivery4.initial_states⟩
    · exact ⟨LowBandObjective062Delivery5.data, LowBandObjective062Delivery5.checked, LowBandObjective062Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate062
