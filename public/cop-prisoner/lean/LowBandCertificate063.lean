import LowBandObjective063Transfer
import LowBandObjective063Delivery0
import LowBandObjective063Delivery1
import LowBandObjective063Delivery2
import LowBandObjective063Delivery3
import LowBandObjective063Delivery4
import LowBandObjective063Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate063
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern063.pattern := by
  constructor
  · exact ⟨LowBandObjective063Transfer.data, LowBandObjective063Transfer.checked, LowBandObjective063Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective063Delivery0.data, LowBandObjective063Delivery0.checked, LowBandObjective063Delivery0.initial_states⟩
    · exact ⟨LowBandObjective063Delivery1.data, LowBandObjective063Delivery1.checked, LowBandObjective063Delivery1.initial_states⟩
    · exact ⟨LowBandObjective063Delivery2.data, LowBandObjective063Delivery2.checked, LowBandObjective063Delivery2.initial_states⟩
    · exact ⟨LowBandObjective063Delivery3.data, LowBandObjective063Delivery3.checked, LowBandObjective063Delivery3.initial_states⟩
    · exact ⟨LowBandObjective063Delivery4.data, LowBandObjective063Delivery4.checked, LowBandObjective063Delivery4.initial_states⟩
    · exact ⟨LowBandObjective063Delivery5.data, LowBandObjective063Delivery5.checked, LowBandObjective063Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate063
