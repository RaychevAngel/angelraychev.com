import LowBandObjective082Transfer
import LowBandObjective082Delivery0
import LowBandObjective082Delivery1
import LowBandObjective082Delivery2
import LowBandObjective082Delivery3
import LowBandObjective082Delivery4
import LowBandObjective082Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate082
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern082.pattern := by
  constructor
  · exact ⟨LowBandObjective082Transfer.data, LowBandObjective082Transfer.checked, LowBandObjective082Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective082Delivery0.data, LowBandObjective082Delivery0.checked, LowBandObjective082Delivery0.initial_states⟩
    · exact ⟨LowBandObjective082Delivery1.data, LowBandObjective082Delivery1.checked, LowBandObjective082Delivery1.initial_states⟩
    · exact ⟨LowBandObjective082Delivery2.data, LowBandObjective082Delivery2.checked, LowBandObjective082Delivery2.initial_states⟩
    · exact ⟨LowBandObjective082Delivery3.data, LowBandObjective082Delivery3.checked, LowBandObjective082Delivery3.initial_states⟩
    · exact ⟨LowBandObjective082Delivery4.data, LowBandObjective082Delivery4.checked, LowBandObjective082Delivery4.initial_states⟩
    · exact ⟨LowBandObjective082Delivery5.data, LowBandObjective082Delivery5.checked, LowBandObjective082Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate082
