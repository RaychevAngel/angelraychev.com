import LowBandObjective098Transfer
import LowBandObjective098Delivery0
import LowBandObjective098Delivery1
import LowBandObjective098Delivery2
import LowBandObjective098Delivery3
import LowBandObjective098Delivery4
import LowBandObjective098Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate098
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern098.pattern := by
  constructor
  · exact ⟨LowBandObjective098Transfer.data, LowBandObjective098Transfer.checked, LowBandObjective098Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective098Delivery0.data, LowBandObjective098Delivery0.checked, LowBandObjective098Delivery0.initial_states⟩
    · exact ⟨LowBandObjective098Delivery1.data, LowBandObjective098Delivery1.checked, LowBandObjective098Delivery1.initial_states⟩
    · exact ⟨LowBandObjective098Delivery2.data, LowBandObjective098Delivery2.checked, LowBandObjective098Delivery2.initial_states⟩
    · exact ⟨LowBandObjective098Delivery3.data, LowBandObjective098Delivery3.checked, LowBandObjective098Delivery3.initial_states⟩
    · exact ⟨LowBandObjective098Delivery4.data, LowBandObjective098Delivery4.checked, LowBandObjective098Delivery4.initial_states⟩
    · exact ⟨LowBandObjective098Delivery5.data, LowBandObjective098Delivery5.checked, LowBandObjective098Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate098
