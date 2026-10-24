import LowBandObjective059Transfer
import LowBandObjective059Delivery0
import LowBandObjective059Delivery1
import LowBandObjective059Delivery2
import LowBandObjective059Delivery3
import LowBandObjective059Delivery4
import LowBandObjective059Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate059
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern059.pattern := by
  constructor
  · exact ⟨LowBandObjective059Transfer.data, LowBandObjective059Transfer.checked, LowBandObjective059Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective059Delivery0.data, LowBandObjective059Delivery0.checked, LowBandObjective059Delivery0.initial_states⟩
    · exact ⟨LowBandObjective059Delivery1.data, LowBandObjective059Delivery1.checked, LowBandObjective059Delivery1.initial_states⟩
    · exact ⟨LowBandObjective059Delivery2.data, LowBandObjective059Delivery2.checked, LowBandObjective059Delivery2.initial_states⟩
    · exact ⟨LowBandObjective059Delivery3.data, LowBandObjective059Delivery3.checked, LowBandObjective059Delivery3.initial_states⟩
    · exact ⟨LowBandObjective059Delivery4.data, LowBandObjective059Delivery4.checked, LowBandObjective059Delivery4.initial_states⟩
    · exact ⟨LowBandObjective059Delivery5.data, LowBandObjective059Delivery5.checked, LowBandObjective059Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate059
