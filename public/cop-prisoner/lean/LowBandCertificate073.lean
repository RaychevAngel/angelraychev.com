import LowBandObjective073Transfer
import LowBandObjective073Delivery0
import LowBandObjective073Delivery1
import LowBandObjective073Delivery2
import LowBandObjective073Delivery3
import LowBandObjective073Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate073
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern073.pattern := by
  constructor
  · exact ⟨LowBandObjective073Transfer.data, LowBandObjective073Transfer.checked, LowBandObjective073Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective073Delivery0.data, LowBandObjective073Delivery0.checked, LowBandObjective073Delivery0.initial_states⟩
    · exact ⟨LowBandObjective073Delivery1.data, LowBandObjective073Delivery1.checked, LowBandObjective073Delivery1.initial_states⟩
    · exact ⟨LowBandObjective073Delivery2.data, LowBandObjective073Delivery2.checked, LowBandObjective073Delivery2.initial_states⟩
    · exact ⟨LowBandObjective073Delivery3.data, LowBandObjective073Delivery3.checked, LowBandObjective073Delivery3.initial_states⟩
    · simp [LowBandPattern073.pattern] at present
    · exact ⟨LowBandObjective073Delivery5.data, LowBandObjective073Delivery5.checked, LowBandObjective073Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate073
