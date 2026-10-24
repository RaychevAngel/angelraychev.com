import LowBandObjective089Transfer
import LowBandObjective089Delivery0
import LowBandObjective089Delivery1
import LowBandObjective089Delivery2
import LowBandObjective089Delivery3
import LowBandObjective089Delivery4
import LowBandObjective089Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate089
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern089.pattern := by
  constructor
  · exact ⟨LowBandObjective089Transfer.data, LowBandObjective089Transfer.checked, LowBandObjective089Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective089Delivery0.data, LowBandObjective089Delivery0.checked, LowBandObjective089Delivery0.initial_states⟩
    · exact ⟨LowBandObjective089Delivery1.data, LowBandObjective089Delivery1.checked, LowBandObjective089Delivery1.initial_states⟩
    · exact ⟨LowBandObjective089Delivery2.data, LowBandObjective089Delivery2.checked, LowBandObjective089Delivery2.initial_states⟩
    · exact ⟨LowBandObjective089Delivery3.data, LowBandObjective089Delivery3.checked, LowBandObjective089Delivery3.initial_states⟩
    · exact ⟨LowBandObjective089Delivery4.data, LowBandObjective089Delivery4.checked, LowBandObjective089Delivery4.initial_states⟩
    · exact ⟨LowBandObjective089Delivery5.data, LowBandObjective089Delivery5.checked, LowBandObjective089Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate089
