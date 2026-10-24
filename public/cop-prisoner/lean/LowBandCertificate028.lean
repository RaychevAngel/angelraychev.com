import LowBandObjective028Transfer
import LowBandObjective028Delivery0
import LowBandObjective028Delivery1
import LowBandObjective028Delivery2
import LowBandObjective028Delivery3
import LowBandObjective028Delivery4
import LowBandObjective028Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate028
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern028.pattern := by
  constructor
  · exact ⟨LowBandObjective028Transfer.data, LowBandObjective028Transfer.checked, LowBandObjective028Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective028Delivery0.data, LowBandObjective028Delivery0.checked, LowBandObjective028Delivery0.initial_states⟩
    · exact ⟨LowBandObjective028Delivery1.data, LowBandObjective028Delivery1.checked, LowBandObjective028Delivery1.initial_states⟩
    · exact ⟨LowBandObjective028Delivery2.data, LowBandObjective028Delivery2.checked, LowBandObjective028Delivery2.initial_states⟩
    · exact ⟨LowBandObjective028Delivery3.data, LowBandObjective028Delivery3.checked, LowBandObjective028Delivery3.initial_states⟩
    · exact ⟨LowBandObjective028Delivery4.data, LowBandObjective028Delivery4.checked, LowBandObjective028Delivery4.initial_states⟩
    · exact ⟨LowBandObjective028Delivery5.data, LowBandObjective028Delivery5.checked, LowBandObjective028Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate028
