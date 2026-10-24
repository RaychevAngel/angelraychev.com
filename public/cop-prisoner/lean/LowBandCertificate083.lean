import LowBandObjective083Transfer
import LowBandObjective083Delivery0
import LowBandObjective083Delivery1
import LowBandObjective083Delivery2
import LowBandObjective083Delivery3
import LowBandObjective083Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate083
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern083.pattern := by
  constructor
  · exact ⟨LowBandObjective083Transfer.data, LowBandObjective083Transfer.checked, LowBandObjective083Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective083Delivery0.data, LowBandObjective083Delivery0.checked, LowBandObjective083Delivery0.initial_states⟩
    · exact ⟨LowBandObjective083Delivery1.data, LowBandObjective083Delivery1.checked, LowBandObjective083Delivery1.initial_states⟩
    · exact ⟨LowBandObjective083Delivery2.data, LowBandObjective083Delivery2.checked, LowBandObjective083Delivery2.initial_states⟩
    · exact ⟨LowBandObjective083Delivery3.data, LowBandObjective083Delivery3.checked, LowBandObjective083Delivery3.initial_states⟩
    · simp [LowBandPattern083.pattern] at present
    · exact ⟨LowBandObjective083Delivery5.data, LowBandObjective083Delivery5.checked, LowBandObjective083Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate083
