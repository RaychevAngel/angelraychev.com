import LowBandObjective022Transfer
import LowBandObjective022Delivery0
import LowBandObjective022Delivery1
import LowBandObjective022Delivery2
import LowBandObjective022Delivery3
import LowBandObjective022Delivery4
import LowBandObjective022Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate022
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern022.pattern := by
  constructor
  · exact ⟨LowBandObjective022Transfer.data, LowBandObjective022Transfer.checked, LowBandObjective022Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective022Delivery0.data, LowBandObjective022Delivery0.checked, LowBandObjective022Delivery0.initial_states⟩
    · exact ⟨LowBandObjective022Delivery1.data, LowBandObjective022Delivery1.checked, LowBandObjective022Delivery1.initial_states⟩
    · exact ⟨LowBandObjective022Delivery2.data, LowBandObjective022Delivery2.checked, LowBandObjective022Delivery2.initial_states⟩
    · exact ⟨LowBandObjective022Delivery3.data, LowBandObjective022Delivery3.checked, LowBandObjective022Delivery3.initial_states⟩
    · exact ⟨LowBandObjective022Delivery4.data, LowBandObjective022Delivery4.checked, LowBandObjective022Delivery4.initial_states⟩
    · exact ⟨LowBandObjective022Delivery5.data, LowBandObjective022Delivery5.checked, LowBandObjective022Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate022
