import LowBandObjective000Transfer
import LowBandObjective000Delivery0
import LowBandObjective000Delivery1
import LowBandObjective000Delivery2
import LowBandObjective000Delivery3
import LowBandObjective000Delivery4
import LowBandObjective000Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate000
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern000.pattern := by
  constructor
  · exact ⟨LowBandObjective000Transfer.data, LowBandObjective000Transfer.checked, LowBandObjective000Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective000Delivery0.data, LowBandObjective000Delivery0.checked, LowBandObjective000Delivery0.initial_states⟩
    · exact ⟨LowBandObjective000Delivery1.data, LowBandObjective000Delivery1.checked, LowBandObjective000Delivery1.initial_states⟩
    · exact ⟨LowBandObjective000Delivery2.data, LowBandObjective000Delivery2.checked, LowBandObjective000Delivery2.initial_states⟩
    · exact ⟨LowBandObjective000Delivery3.data, LowBandObjective000Delivery3.checked, LowBandObjective000Delivery3.initial_states⟩
    · exact ⟨LowBandObjective000Delivery4.data, LowBandObjective000Delivery4.checked, LowBandObjective000Delivery4.initial_states⟩
    · exact ⟨LowBandObjective000Delivery5.data, LowBandObjective000Delivery5.checked, LowBandObjective000Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate000
