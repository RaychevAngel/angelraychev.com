import LowBandObjective008Transfer
import LowBandObjective008Delivery0
import LowBandObjective008Delivery1
import LowBandObjective008Delivery2
import LowBandObjective008Delivery3
import LowBandObjective008Delivery4
import LowBandObjective008Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate008
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern008.pattern := by
  constructor
  · exact ⟨LowBandObjective008Transfer.data, LowBandObjective008Transfer.checked, LowBandObjective008Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective008Delivery0.data, LowBandObjective008Delivery0.checked, LowBandObjective008Delivery0.initial_states⟩
    · exact ⟨LowBandObjective008Delivery1.data, LowBandObjective008Delivery1.checked, LowBandObjective008Delivery1.initial_states⟩
    · exact ⟨LowBandObjective008Delivery2.data, LowBandObjective008Delivery2.checked, LowBandObjective008Delivery2.initial_states⟩
    · exact ⟨LowBandObjective008Delivery3.data, LowBandObjective008Delivery3.checked, LowBandObjective008Delivery3.initial_states⟩
    · exact ⟨LowBandObjective008Delivery4.data, LowBandObjective008Delivery4.checked, LowBandObjective008Delivery4.initial_states⟩
    · exact ⟨LowBandObjective008Delivery5.data, LowBandObjective008Delivery5.checked, LowBandObjective008Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate008
