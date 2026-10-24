import LowBandObjective064Transfer
import LowBandObjective064Delivery0
import LowBandObjective064Delivery1
import LowBandObjective064Delivery2
import LowBandObjective064Delivery3
import LowBandObjective064Delivery4
import LowBandObjective064Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate064
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern064.pattern := by
  constructor
  · exact ⟨LowBandObjective064Transfer.data, LowBandObjective064Transfer.checked, LowBandObjective064Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective064Delivery0.data, LowBandObjective064Delivery0.checked, LowBandObjective064Delivery0.initial_states⟩
    · exact ⟨LowBandObjective064Delivery1.data, LowBandObjective064Delivery1.checked, LowBandObjective064Delivery1.initial_states⟩
    · exact ⟨LowBandObjective064Delivery2.data, LowBandObjective064Delivery2.checked, LowBandObjective064Delivery2.initial_states⟩
    · exact ⟨LowBandObjective064Delivery3.data, LowBandObjective064Delivery3.checked, LowBandObjective064Delivery3.initial_states⟩
    · exact ⟨LowBandObjective064Delivery4.data, LowBandObjective064Delivery4.checked, LowBandObjective064Delivery4.initial_states⟩
    · exact ⟨LowBandObjective064Delivery5.data, LowBandObjective064Delivery5.checked, LowBandObjective064Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate064
