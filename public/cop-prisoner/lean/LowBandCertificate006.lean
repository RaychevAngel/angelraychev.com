import LowBandObjective006Transfer
import LowBandObjective006Delivery0
import LowBandObjective006Delivery1
import LowBandObjective006Delivery2
import LowBandObjective006Delivery3
import LowBandObjective006Delivery4
import LowBandObjective006Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate006
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern006.pattern := by
  constructor
  · exact ⟨LowBandObjective006Transfer.data, LowBandObjective006Transfer.checked, LowBandObjective006Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective006Delivery0.data, LowBandObjective006Delivery0.checked, LowBandObjective006Delivery0.initial_states⟩
    · exact ⟨LowBandObjective006Delivery1.data, LowBandObjective006Delivery1.checked, LowBandObjective006Delivery1.initial_states⟩
    · exact ⟨LowBandObjective006Delivery2.data, LowBandObjective006Delivery2.checked, LowBandObjective006Delivery2.initial_states⟩
    · exact ⟨LowBandObjective006Delivery3.data, LowBandObjective006Delivery3.checked, LowBandObjective006Delivery3.initial_states⟩
    · exact ⟨LowBandObjective006Delivery4.data, LowBandObjective006Delivery4.checked, LowBandObjective006Delivery4.initial_states⟩
    · exact ⟨LowBandObjective006Delivery5.data, LowBandObjective006Delivery5.checked, LowBandObjective006Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate006
