import LowBandObjective048Transfer
import LowBandObjective048Delivery0
import LowBandObjective048Delivery1
import LowBandObjective048Delivery2
import LowBandObjective048Delivery3
import LowBandObjective048Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate048
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern048.pattern := by
  constructor
  · exact ⟨LowBandObjective048Transfer.data, LowBandObjective048Transfer.checked, LowBandObjective048Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective048Delivery0.data, LowBandObjective048Delivery0.checked, LowBandObjective048Delivery0.initial_states⟩
    · exact ⟨LowBandObjective048Delivery1.data, LowBandObjective048Delivery1.checked, LowBandObjective048Delivery1.initial_states⟩
    · exact ⟨LowBandObjective048Delivery2.data, LowBandObjective048Delivery2.checked, LowBandObjective048Delivery2.initial_states⟩
    · exact ⟨LowBandObjective048Delivery3.data, LowBandObjective048Delivery3.checked, LowBandObjective048Delivery3.initial_states⟩
    · simp [LowBandPattern048.pattern] at present
    · exact ⟨LowBandObjective048Delivery5.data, LowBandObjective048Delivery5.checked, LowBandObjective048Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate048
