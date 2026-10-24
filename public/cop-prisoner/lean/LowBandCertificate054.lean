import LowBandObjective054Transfer
import LowBandObjective054Delivery0
import LowBandObjective054Delivery1
import LowBandObjective054Delivery2
import LowBandObjective054Delivery3
import LowBandObjective054Delivery4
import LowBandObjective054Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate054
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern054.pattern := by
  constructor
  · exact ⟨LowBandObjective054Transfer.data, LowBandObjective054Transfer.checked, LowBandObjective054Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective054Delivery0.data, LowBandObjective054Delivery0.checked, LowBandObjective054Delivery0.initial_states⟩
    · exact ⟨LowBandObjective054Delivery1.data, LowBandObjective054Delivery1.checked, LowBandObjective054Delivery1.initial_states⟩
    · exact ⟨LowBandObjective054Delivery2.data, LowBandObjective054Delivery2.checked, LowBandObjective054Delivery2.initial_states⟩
    · exact ⟨LowBandObjective054Delivery3.data, LowBandObjective054Delivery3.checked, LowBandObjective054Delivery3.initial_states⟩
    · exact ⟨LowBandObjective054Delivery4.data, LowBandObjective054Delivery4.checked, LowBandObjective054Delivery4.initial_states⟩
    · exact ⟨LowBandObjective054Delivery5.data, LowBandObjective054Delivery5.checked, LowBandObjective054Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate054
