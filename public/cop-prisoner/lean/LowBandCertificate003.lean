import LowBandObjective003Transfer
import LowBandObjective003Delivery0
import LowBandObjective003Delivery1
import LowBandObjective003Delivery2
import LowBandObjective003Delivery3
import LowBandObjective003Delivery4
import LowBandObjective003Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate003
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern003.pattern := by
  constructor
  · exact ⟨LowBandObjective003Transfer.data, LowBandObjective003Transfer.checked, LowBandObjective003Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective003Delivery0.data, LowBandObjective003Delivery0.checked, LowBandObjective003Delivery0.initial_states⟩
    · exact ⟨LowBandObjective003Delivery1.data, LowBandObjective003Delivery1.checked, LowBandObjective003Delivery1.initial_states⟩
    · exact ⟨LowBandObjective003Delivery2.data, LowBandObjective003Delivery2.checked, LowBandObjective003Delivery2.initial_states⟩
    · exact ⟨LowBandObjective003Delivery3.data, LowBandObjective003Delivery3.checked, LowBandObjective003Delivery3.initial_states⟩
    · exact ⟨LowBandObjective003Delivery4.data, LowBandObjective003Delivery4.checked, LowBandObjective003Delivery4.initial_states⟩
    · exact ⟨LowBandObjective003Delivery5.data, LowBandObjective003Delivery5.checked, LowBandObjective003Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate003
