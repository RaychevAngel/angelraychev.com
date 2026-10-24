import LowBandObjective055Transfer
import LowBandObjective055Delivery0
import LowBandObjective055Delivery1
import LowBandObjective055Delivery2
import LowBandObjective055Delivery3
import LowBandObjective055Delivery4
import LowBandObjective055Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate055
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern055.pattern := by
  constructor
  · exact ⟨LowBandObjective055Transfer.data, LowBandObjective055Transfer.checked, LowBandObjective055Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective055Delivery0.data, LowBandObjective055Delivery0.checked, LowBandObjective055Delivery0.initial_states⟩
    · exact ⟨LowBandObjective055Delivery1.data, LowBandObjective055Delivery1.checked, LowBandObjective055Delivery1.initial_states⟩
    · exact ⟨LowBandObjective055Delivery2.data, LowBandObjective055Delivery2.checked, LowBandObjective055Delivery2.initial_states⟩
    · exact ⟨LowBandObjective055Delivery3.data, LowBandObjective055Delivery3.checked, LowBandObjective055Delivery3.initial_states⟩
    · exact ⟨LowBandObjective055Delivery4.data, LowBandObjective055Delivery4.checked, LowBandObjective055Delivery4.initial_states⟩
    · exact ⟨LowBandObjective055Delivery5.data, LowBandObjective055Delivery5.checked, LowBandObjective055Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate055
