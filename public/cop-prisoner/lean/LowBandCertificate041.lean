import LowBandObjective041Transfer
import LowBandObjective041Delivery0
import LowBandObjective041Delivery1
import LowBandObjective041Delivery2
import LowBandObjective041Delivery3
import LowBandObjective041Delivery4
import LowBandObjective041Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate041
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern041.pattern := by
  constructor
  · exact ⟨LowBandObjective041Transfer.data, LowBandObjective041Transfer.checked, LowBandObjective041Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective041Delivery0.data, LowBandObjective041Delivery0.checked, LowBandObjective041Delivery0.initial_states⟩
    · exact ⟨LowBandObjective041Delivery1.data, LowBandObjective041Delivery1.checked, LowBandObjective041Delivery1.initial_states⟩
    · exact ⟨LowBandObjective041Delivery2.data, LowBandObjective041Delivery2.checked, LowBandObjective041Delivery2.initial_states⟩
    · exact ⟨LowBandObjective041Delivery3.data, LowBandObjective041Delivery3.checked, LowBandObjective041Delivery3.initial_states⟩
    · exact ⟨LowBandObjective041Delivery4.data, LowBandObjective041Delivery4.checked, LowBandObjective041Delivery4.initial_states⟩
    · exact ⟨LowBandObjective041Delivery5.data, LowBandObjective041Delivery5.checked, LowBandObjective041Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate041
