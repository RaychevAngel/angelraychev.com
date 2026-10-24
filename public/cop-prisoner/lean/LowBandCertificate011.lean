import LowBandObjective011Transfer
import LowBandObjective011Delivery0
import LowBandObjective011Delivery1
import LowBandObjective011Delivery2
import LowBandObjective011Delivery3
import LowBandObjective011Delivery4
import LowBandObjective011Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate011
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern011.pattern := by
  constructor
  · exact ⟨LowBandObjective011Transfer.data, LowBandObjective011Transfer.checked, LowBandObjective011Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective011Delivery0.data, LowBandObjective011Delivery0.checked, LowBandObjective011Delivery0.initial_states⟩
    · exact ⟨LowBandObjective011Delivery1.data, LowBandObjective011Delivery1.checked, LowBandObjective011Delivery1.initial_states⟩
    · exact ⟨LowBandObjective011Delivery2.data, LowBandObjective011Delivery2.checked, LowBandObjective011Delivery2.initial_states⟩
    · exact ⟨LowBandObjective011Delivery3.data, LowBandObjective011Delivery3.checked, LowBandObjective011Delivery3.initial_states⟩
    · exact ⟨LowBandObjective011Delivery4.data, LowBandObjective011Delivery4.checked, LowBandObjective011Delivery4.initial_states⟩
    · exact ⟨LowBandObjective011Delivery5.data, LowBandObjective011Delivery5.checked, LowBandObjective011Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate011
