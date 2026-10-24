import LowBandObjective001Transfer
import LowBandObjective001Delivery0
import LowBandObjective001Delivery1
import LowBandObjective001Delivery2
import LowBandObjective001Delivery3
import LowBandObjective001Delivery4
import LowBandObjective001Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate001
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern001.pattern := by
  constructor
  · exact ⟨LowBandObjective001Transfer.data, LowBandObjective001Transfer.checked, LowBandObjective001Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective001Delivery0.data, LowBandObjective001Delivery0.checked, LowBandObjective001Delivery0.initial_states⟩
    · exact ⟨LowBandObjective001Delivery1.data, LowBandObjective001Delivery1.checked, LowBandObjective001Delivery1.initial_states⟩
    · exact ⟨LowBandObjective001Delivery2.data, LowBandObjective001Delivery2.checked, LowBandObjective001Delivery2.initial_states⟩
    · exact ⟨LowBandObjective001Delivery3.data, LowBandObjective001Delivery3.checked, LowBandObjective001Delivery3.initial_states⟩
    · exact ⟨LowBandObjective001Delivery4.data, LowBandObjective001Delivery4.checked, LowBandObjective001Delivery4.initial_states⟩
    · exact ⟨LowBandObjective001Delivery5.data, LowBandObjective001Delivery5.checked, LowBandObjective001Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate001
