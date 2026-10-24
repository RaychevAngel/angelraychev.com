import LowBandObjective046Transfer
import LowBandObjective046Delivery0
import LowBandObjective046Delivery1
import LowBandObjective046Delivery2
import LowBandObjective046Delivery3
import LowBandObjective046Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate046
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern046.pattern := by
  constructor
  · exact ⟨LowBandObjective046Transfer.data, LowBandObjective046Transfer.checked, LowBandObjective046Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective046Delivery0.data, LowBandObjective046Delivery0.checked, LowBandObjective046Delivery0.initial_states⟩
    · exact ⟨LowBandObjective046Delivery1.data, LowBandObjective046Delivery1.checked, LowBandObjective046Delivery1.initial_states⟩
    · exact ⟨LowBandObjective046Delivery2.data, LowBandObjective046Delivery2.checked, LowBandObjective046Delivery2.initial_states⟩
    · exact ⟨LowBandObjective046Delivery3.data, LowBandObjective046Delivery3.checked, LowBandObjective046Delivery3.initial_states⟩
    · simp [LowBandPattern046.pattern] at present
    · exact ⟨LowBandObjective046Delivery5.data, LowBandObjective046Delivery5.checked, LowBandObjective046Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate046
