import LowBandObjective037Transfer
import LowBandObjective037Delivery0
import LowBandObjective037Delivery1
import LowBandObjective037Delivery2
import LowBandObjective037Delivery3
import LowBandObjective037Delivery4
import LowBandObjective037Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate037
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern037.pattern := by
  constructor
  · exact ⟨LowBandObjective037Transfer.data, LowBandObjective037Transfer.checked, LowBandObjective037Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective037Delivery0.data, LowBandObjective037Delivery0.checked, LowBandObjective037Delivery0.initial_states⟩
    · exact ⟨LowBandObjective037Delivery1.data, LowBandObjective037Delivery1.checked, LowBandObjective037Delivery1.initial_states⟩
    · exact ⟨LowBandObjective037Delivery2.data, LowBandObjective037Delivery2.checked, LowBandObjective037Delivery2.initial_states⟩
    · exact ⟨LowBandObjective037Delivery3.data, LowBandObjective037Delivery3.checked, LowBandObjective037Delivery3.initial_states⟩
    · exact ⟨LowBandObjective037Delivery4.data, LowBandObjective037Delivery4.checked, LowBandObjective037Delivery4.initial_states⟩
    · exact ⟨LowBandObjective037Delivery5.data, LowBandObjective037Delivery5.checked, LowBandObjective037Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate037
