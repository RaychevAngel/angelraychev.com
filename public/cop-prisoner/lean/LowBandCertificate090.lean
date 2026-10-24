import LowBandObjective090Transfer
import LowBandObjective090Delivery0
import LowBandObjective090Delivery1
import LowBandObjective090Delivery2
import LowBandObjective090Delivery3
import LowBandObjective090Delivery4
import LowBandObjective090Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate090
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern090.pattern := by
  constructor
  · exact ⟨LowBandObjective090Transfer.data, LowBandObjective090Transfer.checked, LowBandObjective090Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective090Delivery0.data, LowBandObjective090Delivery0.checked, LowBandObjective090Delivery0.initial_states⟩
    · exact ⟨LowBandObjective090Delivery1.data, LowBandObjective090Delivery1.checked, LowBandObjective090Delivery1.initial_states⟩
    · exact ⟨LowBandObjective090Delivery2.data, LowBandObjective090Delivery2.checked, LowBandObjective090Delivery2.initial_states⟩
    · exact ⟨LowBandObjective090Delivery3.data, LowBandObjective090Delivery3.checked, LowBandObjective090Delivery3.initial_states⟩
    · exact ⟨LowBandObjective090Delivery4.data, LowBandObjective090Delivery4.checked, LowBandObjective090Delivery4.initial_states⟩
    · exact ⟨LowBandObjective090Delivery5.data, LowBandObjective090Delivery5.checked, LowBandObjective090Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate090
