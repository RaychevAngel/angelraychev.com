import LowBandObjective029Transfer
import LowBandObjective029Delivery0
import LowBandObjective029Delivery1
import LowBandObjective029Delivery2
import LowBandObjective029Delivery3
import LowBandObjective029Delivery4
import LowBandObjective029Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate029
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern029.pattern := by
  constructor
  · exact ⟨LowBandObjective029Transfer.data, LowBandObjective029Transfer.checked, LowBandObjective029Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective029Delivery0.data, LowBandObjective029Delivery0.checked, LowBandObjective029Delivery0.initial_states⟩
    · exact ⟨LowBandObjective029Delivery1.data, LowBandObjective029Delivery1.checked, LowBandObjective029Delivery1.initial_states⟩
    · exact ⟨LowBandObjective029Delivery2.data, LowBandObjective029Delivery2.checked, LowBandObjective029Delivery2.initial_states⟩
    · exact ⟨LowBandObjective029Delivery3.data, LowBandObjective029Delivery3.checked, LowBandObjective029Delivery3.initial_states⟩
    · exact ⟨LowBandObjective029Delivery4.data, LowBandObjective029Delivery4.checked, LowBandObjective029Delivery4.initial_states⟩
    · exact ⟨LowBandObjective029Delivery5.data, LowBandObjective029Delivery5.checked, LowBandObjective029Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate029
