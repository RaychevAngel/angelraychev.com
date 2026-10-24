import LowBandObjective042Transfer
import LowBandObjective042Delivery0
import LowBandObjective042Delivery1
import LowBandObjective042Delivery2
import LowBandObjective042Delivery3
import LowBandObjective042Delivery4
import LowBandObjective042Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate042
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern042.pattern := by
  constructor
  · exact ⟨LowBandObjective042Transfer.data, LowBandObjective042Transfer.checked, LowBandObjective042Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective042Delivery0.data, LowBandObjective042Delivery0.checked, LowBandObjective042Delivery0.initial_states⟩
    · exact ⟨LowBandObjective042Delivery1.data, LowBandObjective042Delivery1.checked, LowBandObjective042Delivery1.initial_states⟩
    · exact ⟨LowBandObjective042Delivery2.data, LowBandObjective042Delivery2.checked, LowBandObjective042Delivery2.initial_states⟩
    · exact ⟨LowBandObjective042Delivery3.data, LowBandObjective042Delivery3.checked, LowBandObjective042Delivery3.initial_states⟩
    · exact ⟨LowBandObjective042Delivery4.data, LowBandObjective042Delivery4.checked, LowBandObjective042Delivery4.initial_states⟩
    · exact ⟨LowBandObjective042Delivery5.data, LowBandObjective042Delivery5.checked, LowBandObjective042Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate042
