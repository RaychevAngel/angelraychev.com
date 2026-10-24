import LowBandObjective021Transfer
import LowBandObjective021Delivery0
import LowBandObjective021Delivery1
import LowBandObjective021Delivery2
import LowBandObjective021Delivery3
import LowBandObjective021Delivery4
import LowBandObjective021Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate021
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern021.pattern := by
  constructor
  · exact ⟨LowBandObjective021Transfer.data, LowBandObjective021Transfer.checked, LowBandObjective021Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective021Delivery0.data, LowBandObjective021Delivery0.checked, LowBandObjective021Delivery0.initial_states⟩
    · exact ⟨LowBandObjective021Delivery1.data, LowBandObjective021Delivery1.checked, LowBandObjective021Delivery1.initial_states⟩
    · exact ⟨LowBandObjective021Delivery2.data, LowBandObjective021Delivery2.checked, LowBandObjective021Delivery2.initial_states⟩
    · exact ⟨LowBandObjective021Delivery3.data, LowBandObjective021Delivery3.checked, LowBandObjective021Delivery3.initial_states⟩
    · exact ⟨LowBandObjective021Delivery4.data, LowBandObjective021Delivery4.checked, LowBandObjective021Delivery4.initial_states⟩
    · exact ⟨LowBandObjective021Delivery5.data, LowBandObjective021Delivery5.checked, LowBandObjective021Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate021
