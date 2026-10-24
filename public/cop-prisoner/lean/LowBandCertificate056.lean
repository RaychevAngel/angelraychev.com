import LowBandObjective056Transfer
import LowBandObjective056Delivery0
import LowBandObjective056Delivery1
import LowBandObjective056Delivery2
import LowBandObjective056Delivery3
import LowBandObjective056Delivery4
import LowBandObjective056Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate056
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern056.pattern := by
  constructor
  · exact ⟨LowBandObjective056Transfer.data, LowBandObjective056Transfer.checked, LowBandObjective056Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective056Delivery0.data, LowBandObjective056Delivery0.checked, LowBandObjective056Delivery0.initial_states⟩
    · exact ⟨LowBandObjective056Delivery1.data, LowBandObjective056Delivery1.checked, LowBandObjective056Delivery1.initial_states⟩
    · exact ⟨LowBandObjective056Delivery2.data, LowBandObjective056Delivery2.checked, LowBandObjective056Delivery2.initial_states⟩
    · exact ⟨LowBandObjective056Delivery3.data, LowBandObjective056Delivery3.checked, LowBandObjective056Delivery3.initial_states⟩
    · exact ⟨LowBandObjective056Delivery4.data, LowBandObjective056Delivery4.checked, LowBandObjective056Delivery4.initial_states⟩
    · exact ⟨LowBandObjective056Delivery5.data, LowBandObjective056Delivery5.checked, LowBandObjective056Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate056
