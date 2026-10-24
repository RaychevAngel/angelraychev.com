import LowBandObjective036Transfer
import LowBandObjective036Delivery0
import LowBandObjective036Delivery1
import LowBandObjective036Delivery2
import LowBandObjective036Delivery3
import LowBandObjective036Delivery4
import LowBandObjective036Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate036
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern036.pattern := by
  constructor
  · exact ⟨LowBandObjective036Transfer.data, LowBandObjective036Transfer.checked, LowBandObjective036Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective036Delivery0.data, LowBandObjective036Delivery0.checked, LowBandObjective036Delivery0.initial_states⟩
    · exact ⟨LowBandObjective036Delivery1.data, LowBandObjective036Delivery1.checked, LowBandObjective036Delivery1.initial_states⟩
    · exact ⟨LowBandObjective036Delivery2.data, LowBandObjective036Delivery2.checked, LowBandObjective036Delivery2.initial_states⟩
    · exact ⟨LowBandObjective036Delivery3.data, LowBandObjective036Delivery3.checked, LowBandObjective036Delivery3.initial_states⟩
    · exact ⟨LowBandObjective036Delivery4.data, LowBandObjective036Delivery4.checked, LowBandObjective036Delivery4.initial_states⟩
    · exact ⟨LowBandObjective036Delivery5.data, LowBandObjective036Delivery5.checked, LowBandObjective036Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate036
