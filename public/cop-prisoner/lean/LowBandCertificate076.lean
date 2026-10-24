import LowBandObjective076Transfer
import LowBandObjective076Delivery0
import LowBandObjective076Delivery1
import LowBandObjective076Delivery2
import LowBandObjective076Delivery3
import LowBandObjective076Delivery4
import LowBandObjective076Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate076
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern076.pattern := by
  constructor
  · exact ⟨LowBandObjective076Transfer.data, LowBandObjective076Transfer.checked, LowBandObjective076Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective076Delivery0.data, LowBandObjective076Delivery0.checked, LowBandObjective076Delivery0.initial_states⟩
    · exact ⟨LowBandObjective076Delivery1.data, LowBandObjective076Delivery1.checked, LowBandObjective076Delivery1.initial_states⟩
    · exact ⟨LowBandObjective076Delivery2.data, LowBandObjective076Delivery2.checked, LowBandObjective076Delivery2.initial_states⟩
    · exact ⟨LowBandObjective076Delivery3.data, LowBandObjective076Delivery3.checked, LowBandObjective076Delivery3.initial_states⟩
    · exact ⟨LowBandObjective076Delivery4.data, LowBandObjective076Delivery4.checked, LowBandObjective076Delivery4.initial_states⟩
    · exact ⟨LowBandObjective076Delivery5.data, LowBandObjective076Delivery5.checked, LowBandObjective076Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate076
