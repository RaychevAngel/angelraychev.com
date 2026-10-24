import LowBandObjective014Transfer
import LowBandObjective014Delivery0
import LowBandObjective014Delivery1
import LowBandObjective014Delivery2
import LowBandObjective014Delivery3
import LowBandObjective014Delivery4
import LowBandObjective014Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate014
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern014.pattern := by
  constructor
  · exact ⟨LowBandObjective014Transfer.data, LowBandObjective014Transfer.checked, LowBandObjective014Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective014Delivery0.data, LowBandObjective014Delivery0.checked, LowBandObjective014Delivery0.initial_states⟩
    · exact ⟨LowBandObjective014Delivery1.data, LowBandObjective014Delivery1.checked, LowBandObjective014Delivery1.initial_states⟩
    · exact ⟨LowBandObjective014Delivery2.data, LowBandObjective014Delivery2.checked, LowBandObjective014Delivery2.initial_states⟩
    · exact ⟨LowBandObjective014Delivery3.data, LowBandObjective014Delivery3.checked, LowBandObjective014Delivery3.initial_states⟩
    · exact ⟨LowBandObjective014Delivery4.data, LowBandObjective014Delivery4.checked, LowBandObjective014Delivery4.initial_states⟩
    · exact ⟨LowBandObjective014Delivery5.data, LowBandObjective014Delivery5.checked, LowBandObjective014Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate014
