import LowBandObjective093Transfer
import LowBandObjective093Delivery0
import LowBandObjective093Delivery1
import LowBandObjective093Delivery2
import LowBandObjective093Delivery3
import LowBandObjective093Delivery4
import LowBandObjective093Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate093
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern093.pattern := by
  constructor
  · exact ⟨LowBandObjective093Transfer.data, LowBandObjective093Transfer.checked, LowBandObjective093Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective093Delivery0.data, LowBandObjective093Delivery0.checked, LowBandObjective093Delivery0.initial_states⟩
    · exact ⟨LowBandObjective093Delivery1.data, LowBandObjective093Delivery1.checked, LowBandObjective093Delivery1.initial_states⟩
    · exact ⟨LowBandObjective093Delivery2.data, LowBandObjective093Delivery2.checked, LowBandObjective093Delivery2.initial_states⟩
    · exact ⟨LowBandObjective093Delivery3.data, LowBandObjective093Delivery3.checked, LowBandObjective093Delivery3.initial_states⟩
    · exact ⟨LowBandObjective093Delivery4.data, LowBandObjective093Delivery4.checked, LowBandObjective093Delivery4.initial_states⟩
    · exact ⟨LowBandObjective093Delivery5.data, LowBandObjective093Delivery5.checked, LowBandObjective093Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate093
