import LowBandObjective033Transfer
import LowBandObjective033Delivery0
import LowBandObjective033Delivery1
import LowBandObjective033Delivery2
import LowBandObjective033Delivery3
import LowBandObjective033Delivery4
import LowBandObjective033Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate033
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern033.pattern := by
  constructor
  · exact ⟨LowBandObjective033Transfer.data, LowBandObjective033Transfer.checked, LowBandObjective033Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective033Delivery0.data, LowBandObjective033Delivery0.checked, LowBandObjective033Delivery0.initial_states⟩
    · exact ⟨LowBandObjective033Delivery1.data, LowBandObjective033Delivery1.checked, LowBandObjective033Delivery1.initial_states⟩
    · exact ⟨LowBandObjective033Delivery2.data, LowBandObjective033Delivery2.checked, LowBandObjective033Delivery2.initial_states⟩
    · exact ⟨LowBandObjective033Delivery3.data, LowBandObjective033Delivery3.checked, LowBandObjective033Delivery3.initial_states⟩
    · exact ⟨LowBandObjective033Delivery4.data, LowBandObjective033Delivery4.checked, LowBandObjective033Delivery4.initial_states⟩
    · exact ⟨LowBandObjective033Delivery5.data, LowBandObjective033Delivery5.checked, LowBandObjective033Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate033
