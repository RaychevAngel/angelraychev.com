import LowBandObjective043Transfer
import LowBandObjective043Delivery0
import LowBandObjective043Delivery1
import LowBandObjective043Delivery2
import LowBandObjective043Delivery3
import LowBandObjective043Delivery4
import LowBandObjective043Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate043
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern043.pattern := by
  constructor
  · exact ⟨LowBandObjective043Transfer.data, LowBandObjective043Transfer.checked, LowBandObjective043Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective043Delivery0.data, LowBandObjective043Delivery0.checked, LowBandObjective043Delivery0.initial_states⟩
    · exact ⟨LowBandObjective043Delivery1.data, LowBandObjective043Delivery1.checked, LowBandObjective043Delivery1.initial_states⟩
    · exact ⟨LowBandObjective043Delivery2.data, LowBandObjective043Delivery2.checked, LowBandObjective043Delivery2.initial_states⟩
    · exact ⟨LowBandObjective043Delivery3.data, LowBandObjective043Delivery3.checked, LowBandObjective043Delivery3.initial_states⟩
    · exact ⟨LowBandObjective043Delivery4.data, LowBandObjective043Delivery4.checked, LowBandObjective043Delivery4.initial_states⟩
    · exact ⟨LowBandObjective043Delivery5.data, LowBandObjective043Delivery5.checked, LowBandObjective043Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate043
