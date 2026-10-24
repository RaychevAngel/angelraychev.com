import LowBandObjective017Transfer
import LowBandObjective017Delivery0
import LowBandObjective017Delivery1
import LowBandObjective017Delivery2
import LowBandObjective017Delivery3
import LowBandObjective017Delivery4
import LowBandObjective017Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate017
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern017.pattern := by
  constructor
  · exact ⟨LowBandObjective017Transfer.data, LowBandObjective017Transfer.checked, LowBandObjective017Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective017Delivery0.data, LowBandObjective017Delivery0.checked, LowBandObjective017Delivery0.initial_states⟩
    · exact ⟨LowBandObjective017Delivery1.data, LowBandObjective017Delivery1.checked, LowBandObjective017Delivery1.initial_states⟩
    · exact ⟨LowBandObjective017Delivery2.data, LowBandObjective017Delivery2.checked, LowBandObjective017Delivery2.initial_states⟩
    · exact ⟨LowBandObjective017Delivery3.data, LowBandObjective017Delivery3.checked, LowBandObjective017Delivery3.initial_states⟩
    · exact ⟨LowBandObjective017Delivery4.data, LowBandObjective017Delivery4.checked, LowBandObjective017Delivery4.initial_states⟩
    · exact ⟨LowBandObjective017Delivery5.data, LowBandObjective017Delivery5.checked, LowBandObjective017Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate017
