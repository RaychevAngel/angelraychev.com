import LowBandObjective040Transfer
import LowBandObjective040Delivery0
import LowBandObjective040Delivery1
import LowBandObjective040Delivery2
import LowBandObjective040Delivery3
import LowBandObjective040Delivery4
import LowBandObjective040Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate040
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern040.pattern := by
  constructor
  · exact ⟨LowBandObjective040Transfer.data, LowBandObjective040Transfer.checked, LowBandObjective040Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective040Delivery0.data, LowBandObjective040Delivery0.checked, LowBandObjective040Delivery0.initial_states⟩
    · exact ⟨LowBandObjective040Delivery1.data, LowBandObjective040Delivery1.checked, LowBandObjective040Delivery1.initial_states⟩
    · exact ⟨LowBandObjective040Delivery2.data, LowBandObjective040Delivery2.checked, LowBandObjective040Delivery2.initial_states⟩
    · exact ⟨LowBandObjective040Delivery3.data, LowBandObjective040Delivery3.checked, LowBandObjective040Delivery3.initial_states⟩
    · exact ⟨LowBandObjective040Delivery4.data, LowBandObjective040Delivery4.checked, LowBandObjective040Delivery4.initial_states⟩
    · exact ⟨LowBandObjective040Delivery5.data, LowBandObjective040Delivery5.checked, LowBandObjective040Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate040
