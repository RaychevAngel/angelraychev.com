import LowBandObjective039Transfer
import LowBandObjective039Delivery0
import LowBandObjective039Delivery1
import LowBandObjective039Delivery2
import LowBandObjective039Delivery3
import LowBandObjective039Delivery4
import LowBandObjective039Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate039
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern039.pattern := by
  constructor
  · exact ⟨LowBandObjective039Transfer.data, LowBandObjective039Transfer.checked, LowBandObjective039Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective039Delivery0.data, LowBandObjective039Delivery0.checked, LowBandObjective039Delivery0.initial_states⟩
    · exact ⟨LowBandObjective039Delivery1.data, LowBandObjective039Delivery1.checked, LowBandObjective039Delivery1.initial_states⟩
    · exact ⟨LowBandObjective039Delivery2.data, LowBandObjective039Delivery2.checked, LowBandObjective039Delivery2.initial_states⟩
    · exact ⟨LowBandObjective039Delivery3.data, LowBandObjective039Delivery3.checked, LowBandObjective039Delivery3.initial_states⟩
    · exact ⟨LowBandObjective039Delivery4.data, LowBandObjective039Delivery4.checked, LowBandObjective039Delivery4.initial_states⟩
    · exact ⟨LowBandObjective039Delivery5.data, LowBandObjective039Delivery5.checked, LowBandObjective039Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate039
