import LowBandObjective016Transfer
import LowBandObjective016Delivery0
import LowBandObjective016Delivery1
import LowBandObjective016Delivery2
import LowBandObjective016Delivery3
import LowBandObjective016Delivery4
import LowBandObjective016Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate016
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern016.pattern := by
  constructor
  · exact ⟨LowBandObjective016Transfer.data, LowBandObjective016Transfer.checked, LowBandObjective016Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective016Delivery0.data, LowBandObjective016Delivery0.checked, LowBandObjective016Delivery0.initial_states⟩
    · exact ⟨LowBandObjective016Delivery1.data, LowBandObjective016Delivery1.checked, LowBandObjective016Delivery1.initial_states⟩
    · exact ⟨LowBandObjective016Delivery2.data, LowBandObjective016Delivery2.checked, LowBandObjective016Delivery2.initial_states⟩
    · exact ⟨LowBandObjective016Delivery3.data, LowBandObjective016Delivery3.checked, LowBandObjective016Delivery3.initial_states⟩
    · exact ⟨LowBandObjective016Delivery4.data, LowBandObjective016Delivery4.checked, LowBandObjective016Delivery4.initial_states⟩
    · exact ⟨LowBandObjective016Delivery5.data, LowBandObjective016Delivery5.checked, LowBandObjective016Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate016
