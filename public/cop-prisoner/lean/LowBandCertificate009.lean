import LowBandObjective009Transfer
import LowBandObjective009Delivery0
import LowBandObjective009Delivery1
import LowBandObjective009Delivery2
import LowBandObjective009Delivery3
import LowBandObjective009Delivery4
import LowBandObjective009Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate009
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern009.pattern := by
  constructor
  · exact ⟨LowBandObjective009Transfer.data, LowBandObjective009Transfer.checked, LowBandObjective009Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective009Delivery0.data, LowBandObjective009Delivery0.checked, LowBandObjective009Delivery0.initial_states⟩
    · exact ⟨LowBandObjective009Delivery1.data, LowBandObjective009Delivery1.checked, LowBandObjective009Delivery1.initial_states⟩
    · exact ⟨LowBandObjective009Delivery2.data, LowBandObjective009Delivery2.checked, LowBandObjective009Delivery2.initial_states⟩
    · exact ⟨LowBandObjective009Delivery3.data, LowBandObjective009Delivery3.checked, LowBandObjective009Delivery3.initial_states⟩
    · exact ⟨LowBandObjective009Delivery4.data, LowBandObjective009Delivery4.checked, LowBandObjective009Delivery4.initial_states⟩
    · exact ⟨LowBandObjective009Delivery5.data, LowBandObjective009Delivery5.checked, LowBandObjective009Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate009
