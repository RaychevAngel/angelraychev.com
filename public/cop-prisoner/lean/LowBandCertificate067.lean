import LowBandObjective067Transfer
import LowBandObjective067Delivery0
import LowBandObjective067Delivery1
import LowBandObjective067Delivery2
import LowBandObjective067Delivery3
import LowBandObjective067Delivery4
import LowBandObjective067Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate067
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern067.pattern := by
  constructor
  · exact ⟨LowBandObjective067Transfer.data, LowBandObjective067Transfer.checked, LowBandObjective067Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective067Delivery0.data, LowBandObjective067Delivery0.checked, LowBandObjective067Delivery0.initial_states⟩
    · exact ⟨LowBandObjective067Delivery1.data, LowBandObjective067Delivery1.checked, LowBandObjective067Delivery1.initial_states⟩
    · exact ⟨LowBandObjective067Delivery2.data, LowBandObjective067Delivery2.checked, LowBandObjective067Delivery2.initial_states⟩
    · exact ⟨LowBandObjective067Delivery3.data, LowBandObjective067Delivery3.checked, LowBandObjective067Delivery3.initial_states⟩
    · exact ⟨LowBandObjective067Delivery4.data, LowBandObjective067Delivery4.checked, LowBandObjective067Delivery4.initial_states⟩
    · exact ⟨LowBandObjective067Delivery5.data, LowBandObjective067Delivery5.checked, LowBandObjective067Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate067
