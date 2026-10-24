import LowBandObjective091Transfer
import LowBandObjective091Delivery0
import LowBandObjective091Delivery1
import LowBandObjective091Delivery2
import LowBandObjective091Delivery3
import LowBandObjective091Delivery4
import LowBandObjective091Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate091
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern091.pattern := by
  constructor
  · exact ⟨LowBandObjective091Transfer.data, LowBandObjective091Transfer.checked, LowBandObjective091Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective091Delivery0.data, LowBandObjective091Delivery0.checked, LowBandObjective091Delivery0.initial_states⟩
    · exact ⟨LowBandObjective091Delivery1.data, LowBandObjective091Delivery1.checked, LowBandObjective091Delivery1.initial_states⟩
    · exact ⟨LowBandObjective091Delivery2.data, LowBandObjective091Delivery2.checked, LowBandObjective091Delivery2.initial_states⟩
    · exact ⟨LowBandObjective091Delivery3.data, LowBandObjective091Delivery3.checked, LowBandObjective091Delivery3.initial_states⟩
    · exact ⟨LowBandObjective091Delivery4.data, LowBandObjective091Delivery4.checked, LowBandObjective091Delivery4.initial_states⟩
    · exact ⟨LowBandObjective091Delivery5.data, LowBandObjective091Delivery5.checked, LowBandObjective091Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate091
