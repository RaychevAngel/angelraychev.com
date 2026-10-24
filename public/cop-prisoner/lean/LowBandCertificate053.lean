import LowBandObjective053Transfer
import LowBandObjective053Delivery0
import LowBandObjective053Delivery1
import LowBandObjective053Delivery2
import LowBandObjective053Delivery3
import LowBandObjective053Delivery4
import LowBandObjective053Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate053
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern053.pattern := by
  constructor
  · exact ⟨LowBandObjective053Transfer.data, LowBandObjective053Transfer.checked, LowBandObjective053Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective053Delivery0.data, LowBandObjective053Delivery0.checked, LowBandObjective053Delivery0.initial_states⟩
    · exact ⟨LowBandObjective053Delivery1.data, LowBandObjective053Delivery1.checked, LowBandObjective053Delivery1.initial_states⟩
    · exact ⟨LowBandObjective053Delivery2.data, LowBandObjective053Delivery2.checked, LowBandObjective053Delivery2.initial_states⟩
    · exact ⟨LowBandObjective053Delivery3.data, LowBandObjective053Delivery3.checked, LowBandObjective053Delivery3.initial_states⟩
    · exact ⟨LowBandObjective053Delivery4.data, LowBandObjective053Delivery4.checked, LowBandObjective053Delivery4.initial_states⟩
    · exact ⟨LowBandObjective053Delivery5.data, LowBandObjective053Delivery5.checked, LowBandObjective053Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate053
