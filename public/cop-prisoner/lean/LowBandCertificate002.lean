import LowBandObjective002Transfer
import LowBandObjective002Delivery0
import LowBandObjective002Delivery1
import LowBandObjective002Delivery2
import LowBandObjective002Delivery3
import LowBandObjective002Delivery4
import LowBandObjective002Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate002
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern002.pattern := by
  constructor
  · exact ⟨LowBandObjective002Transfer.data, LowBandObjective002Transfer.checked, LowBandObjective002Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective002Delivery0.data, LowBandObjective002Delivery0.checked, LowBandObjective002Delivery0.initial_states⟩
    · exact ⟨LowBandObjective002Delivery1.data, LowBandObjective002Delivery1.checked, LowBandObjective002Delivery1.initial_states⟩
    · exact ⟨LowBandObjective002Delivery2.data, LowBandObjective002Delivery2.checked, LowBandObjective002Delivery2.initial_states⟩
    · exact ⟨LowBandObjective002Delivery3.data, LowBandObjective002Delivery3.checked, LowBandObjective002Delivery3.initial_states⟩
    · exact ⟨LowBandObjective002Delivery4.data, LowBandObjective002Delivery4.checked, LowBandObjective002Delivery4.initial_states⟩
    · exact ⟨LowBandObjective002Delivery5.data, LowBandObjective002Delivery5.checked, LowBandObjective002Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate002
