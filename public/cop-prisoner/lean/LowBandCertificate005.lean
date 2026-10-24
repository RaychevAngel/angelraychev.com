import LowBandObjective005Transfer
import LowBandObjective005Delivery0
import LowBandObjective005Delivery1
import LowBandObjective005Delivery2
import LowBandObjective005Delivery3
import LowBandObjective005Delivery4
import LowBandObjective005Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate005
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern005.pattern := by
  constructor
  · exact ⟨LowBandObjective005Transfer.data, LowBandObjective005Transfer.checked, LowBandObjective005Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective005Delivery0.data, LowBandObjective005Delivery0.checked, LowBandObjective005Delivery0.initial_states⟩
    · exact ⟨LowBandObjective005Delivery1.data, LowBandObjective005Delivery1.checked, LowBandObjective005Delivery1.initial_states⟩
    · exact ⟨LowBandObjective005Delivery2.data, LowBandObjective005Delivery2.checked, LowBandObjective005Delivery2.initial_states⟩
    · exact ⟨LowBandObjective005Delivery3.data, LowBandObjective005Delivery3.checked, LowBandObjective005Delivery3.initial_states⟩
    · exact ⟨LowBandObjective005Delivery4.data, LowBandObjective005Delivery4.checked, LowBandObjective005Delivery4.initial_states⟩
    · exact ⟨LowBandObjective005Delivery5.data, LowBandObjective005Delivery5.checked, LowBandObjective005Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate005
