import LowBandObjective079Transfer
import LowBandObjective079Delivery0
import LowBandObjective079Delivery1
import LowBandObjective079Delivery2
import LowBandObjective079Delivery3
import LowBandObjective079Delivery4
import LowBandObjective079Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate079
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern079.pattern := by
  constructor
  · exact ⟨LowBandObjective079Transfer.data, LowBandObjective079Transfer.checked, LowBandObjective079Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective079Delivery0.data, LowBandObjective079Delivery0.checked, LowBandObjective079Delivery0.initial_states⟩
    · exact ⟨LowBandObjective079Delivery1.data, LowBandObjective079Delivery1.checked, LowBandObjective079Delivery1.initial_states⟩
    · exact ⟨LowBandObjective079Delivery2.data, LowBandObjective079Delivery2.checked, LowBandObjective079Delivery2.initial_states⟩
    · exact ⟨LowBandObjective079Delivery3.data, LowBandObjective079Delivery3.checked, LowBandObjective079Delivery3.initial_states⟩
    · exact ⟨LowBandObjective079Delivery4.data, LowBandObjective079Delivery4.checked, LowBandObjective079Delivery4.initial_states⟩
    · exact ⟨LowBandObjective079Delivery5.data, LowBandObjective079Delivery5.checked, LowBandObjective079Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate079
