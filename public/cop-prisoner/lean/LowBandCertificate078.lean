import LowBandObjective078Transfer
import LowBandObjective078Delivery0
import LowBandObjective078Delivery1
import LowBandObjective078Delivery2
import LowBandObjective078Delivery3
import LowBandObjective078Delivery4
import LowBandObjective078Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate078
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern078.pattern := by
  constructor
  · exact ⟨LowBandObjective078Transfer.data, LowBandObjective078Transfer.checked, LowBandObjective078Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective078Delivery0.data, LowBandObjective078Delivery0.checked, LowBandObjective078Delivery0.initial_states⟩
    · exact ⟨LowBandObjective078Delivery1.data, LowBandObjective078Delivery1.checked, LowBandObjective078Delivery1.initial_states⟩
    · exact ⟨LowBandObjective078Delivery2.data, LowBandObjective078Delivery2.checked, LowBandObjective078Delivery2.initial_states⟩
    · exact ⟨LowBandObjective078Delivery3.data, LowBandObjective078Delivery3.checked, LowBandObjective078Delivery3.initial_states⟩
    · exact ⟨LowBandObjective078Delivery4.data, LowBandObjective078Delivery4.checked, LowBandObjective078Delivery4.initial_states⟩
    · exact ⟨LowBandObjective078Delivery5.data, LowBandObjective078Delivery5.checked, LowBandObjective078Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate078
