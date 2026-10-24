import LowBandObjective071Transfer
import LowBandObjective071Delivery0
import LowBandObjective071Delivery1
import LowBandObjective071Delivery2
import LowBandObjective071Delivery3
import LowBandObjective071Delivery4
import LowBandObjective071Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate071
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern071.pattern := by
  constructor
  · exact ⟨LowBandObjective071Transfer.data, LowBandObjective071Transfer.checked, LowBandObjective071Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective071Delivery0.data, LowBandObjective071Delivery0.checked, LowBandObjective071Delivery0.initial_states⟩
    · exact ⟨LowBandObjective071Delivery1.data, LowBandObjective071Delivery1.checked, LowBandObjective071Delivery1.initial_states⟩
    · exact ⟨LowBandObjective071Delivery2.data, LowBandObjective071Delivery2.checked, LowBandObjective071Delivery2.initial_states⟩
    · exact ⟨LowBandObjective071Delivery3.data, LowBandObjective071Delivery3.checked, LowBandObjective071Delivery3.initial_states⟩
    · exact ⟨LowBandObjective071Delivery4.data, LowBandObjective071Delivery4.checked, LowBandObjective071Delivery4.initial_states⟩
    · exact ⟨LowBandObjective071Delivery5.data, LowBandObjective071Delivery5.checked, LowBandObjective071Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate071
