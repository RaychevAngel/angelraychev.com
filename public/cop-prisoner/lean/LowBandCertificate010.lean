import LowBandObjective010Transfer
import LowBandObjective010Delivery0
import LowBandObjective010Delivery1
import LowBandObjective010Delivery2
import LowBandObjective010Delivery3
import LowBandObjective010Delivery4
import LowBandObjective010Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate010
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern010.pattern := by
  constructor
  · exact ⟨LowBandObjective010Transfer.data, LowBandObjective010Transfer.checked, LowBandObjective010Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective010Delivery0.data, LowBandObjective010Delivery0.checked, LowBandObjective010Delivery0.initial_states⟩
    · exact ⟨LowBandObjective010Delivery1.data, LowBandObjective010Delivery1.checked, LowBandObjective010Delivery1.initial_states⟩
    · exact ⟨LowBandObjective010Delivery2.data, LowBandObjective010Delivery2.checked, LowBandObjective010Delivery2.initial_states⟩
    · exact ⟨LowBandObjective010Delivery3.data, LowBandObjective010Delivery3.checked, LowBandObjective010Delivery3.initial_states⟩
    · exact ⟨LowBandObjective010Delivery4.data, LowBandObjective010Delivery4.checked, LowBandObjective010Delivery4.initial_states⟩
    · exact ⟨LowBandObjective010Delivery5.data, LowBandObjective010Delivery5.checked, LowBandObjective010Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate010
