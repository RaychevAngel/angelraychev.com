import LowBandObjective058Transfer
import LowBandObjective058Delivery0
import LowBandObjective058Delivery1
import LowBandObjective058Delivery2
import LowBandObjective058Delivery3
import LowBandObjective058Delivery4
import LowBandObjective058Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate058
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern058.pattern := by
  constructor
  · exact ⟨LowBandObjective058Transfer.data, LowBandObjective058Transfer.checked, LowBandObjective058Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective058Delivery0.data, LowBandObjective058Delivery0.checked, LowBandObjective058Delivery0.initial_states⟩
    · exact ⟨LowBandObjective058Delivery1.data, LowBandObjective058Delivery1.checked, LowBandObjective058Delivery1.initial_states⟩
    · exact ⟨LowBandObjective058Delivery2.data, LowBandObjective058Delivery2.checked, LowBandObjective058Delivery2.initial_states⟩
    · exact ⟨LowBandObjective058Delivery3.data, LowBandObjective058Delivery3.checked, LowBandObjective058Delivery3.initial_states⟩
    · exact ⟨LowBandObjective058Delivery4.data, LowBandObjective058Delivery4.checked, LowBandObjective058Delivery4.initial_states⟩
    · exact ⟨LowBandObjective058Delivery5.data, LowBandObjective058Delivery5.checked, LowBandObjective058Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate058
