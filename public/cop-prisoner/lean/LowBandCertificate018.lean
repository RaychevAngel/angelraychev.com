import LowBandObjective018Transfer
import LowBandObjective018Delivery0
import LowBandObjective018Delivery1
import LowBandObjective018Delivery2
import LowBandObjective018Delivery3
import LowBandObjective018Delivery4
import LowBandObjective018Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate018
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern018.pattern := by
  constructor
  · exact ⟨LowBandObjective018Transfer.data, LowBandObjective018Transfer.checked, LowBandObjective018Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective018Delivery0.data, LowBandObjective018Delivery0.checked, LowBandObjective018Delivery0.initial_states⟩
    · exact ⟨LowBandObjective018Delivery1.data, LowBandObjective018Delivery1.checked, LowBandObjective018Delivery1.initial_states⟩
    · exact ⟨LowBandObjective018Delivery2.data, LowBandObjective018Delivery2.checked, LowBandObjective018Delivery2.initial_states⟩
    · exact ⟨LowBandObjective018Delivery3.data, LowBandObjective018Delivery3.checked, LowBandObjective018Delivery3.initial_states⟩
    · exact ⟨LowBandObjective018Delivery4.data, LowBandObjective018Delivery4.checked, LowBandObjective018Delivery4.initial_states⟩
    · exact ⟨LowBandObjective018Delivery5.data, LowBandObjective018Delivery5.checked, LowBandObjective018Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate018
