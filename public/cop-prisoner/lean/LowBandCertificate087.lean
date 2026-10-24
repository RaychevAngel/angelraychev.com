import LowBandObjective087Transfer
import LowBandObjective087Delivery0
import LowBandObjective087Delivery1
import LowBandObjective087Delivery2
import LowBandObjective087Delivery3
import LowBandObjective087Delivery4
import LowBandObjective087Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate087
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern087.pattern := by
  constructor
  · exact ⟨LowBandObjective087Transfer.data, LowBandObjective087Transfer.checked, LowBandObjective087Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective087Delivery0.data, LowBandObjective087Delivery0.checked, LowBandObjective087Delivery0.initial_states⟩
    · exact ⟨LowBandObjective087Delivery1.data, LowBandObjective087Delivery1.checked, LowBandObjective087Delivery1.initial_states⟩
    · exact ⟨LowBandObjective087Delivery2.data, LowBandObjective087Delivery2.checked, LowBandObjective087Delivery2.initial_states⟩
    · exact ⟨LowBandObjective087Delivery3.data, LowBandObjective087Delivery3.checked, LowBandObjective087Delivery3.initial_states⟩
    · exact ⟨LowBandObjective087Delivery4.data, LowBandObjective087Delivery4.checked, LowBandObjective087Delivery4.initial_states⟩
    · exact ⟨LowBandObjective087Delivery5.data, LowBandObjective087Delivery5.checked, LowBandObjective087Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate087
