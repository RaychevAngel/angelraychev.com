import LowBandObjective052Transfer
import LowBandObjective052Delivery0
import LowBandObjective052Delivery1
import LowBandObjective052Delivery2
import LowBandObjective052Delivery3
import LowBandObjective052Delivery4
import LowBandObjective052Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate052
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern052.pattern := by
  constructor
  · exact ⟨LowBandObjective052Transfer.data, LowBandObjective052Transfer.checked, LowBandObjective052Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective052Delivery0.data, LowBandObjective052Delivery0.checked, LowBandObjective052Delivery0.initial_states⟩
    · exact ⟨LowBandObjective052Delivery1.data, LowBandObjective052Delivery1.checked, LowBandObjective052Delivery1.initial_states⟩
    · exact ⟨LowBandObjective052Delivery2.data, LowBandObjective052Delivery2.checked, LowBandObjective052Delivery2.initial_states⟩
    · exact ⟨LowBandObjective052Delivery3.data, LowBandObjective052Delivery3.checked, LowBandObjective052Delivery3.initial_states⟩
    · exact ⟨LowBandObjective052Delivery4.data, LowBandObjective052Delivery4.checked, LowBandObjective052Delivery4.initial_states⟩
    · exact ⟨LowBandObjective052Delivery5.data, LowBandObjective052Delivery5.checked, LowBandObjective052Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate052
