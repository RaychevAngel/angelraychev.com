import LowBandObjective075Transfer
import LowBandObjective075Delivery0
import LowBandObjective075Delivery1
import LowBandObjective075Delivery2
import LowBandObjective075Delivery3
import LowBandObjective075Delivery4
import LowBandObjective075Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate075
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern075.pattern := by
  constructor
  · exact ⟨LowBandObjective075Transfer.data, LowBandObjective075Transfer.checked, LowBandObjective075Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective075Delivery0.data, LowBandObjective075Delivery0.checked, LowBandObjective075Delivery0.initial_states⟩
    · exact ⟨LowBandObjective075Delivery1.data, LowBandObjective075Delivery1.checked, LowBandObjective075Delivery1.initial_states⟩
    · exact ⟨LowBandObjective075Delivery2.data, LowBandObjective075Delivery2.checked, LowBandObjective075Delivery2.initial_states⟩
    · exact ⟨LowBandObjective075Delivery3.data, LowBandObjective075Delivery3.checked, LowBandObjective075Delivery3.initial_states⟩
    · exact ⟨LowBandObjective075Delivery4.data, LowBandObjective075Delivery4.checked, LowBandObjective075Delivery4.initial_states⟩
    · exact ⟨LowBandObjective075Delivery5.data, LowBandObjective075Delivery5.checked, LowBandObjective075Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate075
