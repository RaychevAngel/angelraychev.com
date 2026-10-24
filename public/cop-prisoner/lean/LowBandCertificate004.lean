import LowBandObjective004Transfer
import LowBandObjective004Delivery0
import LowBandObjective004Delivery1
import LowBandObjective004Delivery2
import LowBandObjective004Delivery3
import LowBandObjective004Delivery4
import LowBandObjective004Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate004
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern004.pattern := by
  constructor
  · exact ⟨LowBandObjective004Transfer.data, LowBandObjective004Transfer.checked, LowBandObjective004Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective004Delivery0.data, LowBandObjective004Delivery0.checked, LowBandObjective004Delivery0.initial_states⟩
    · exact ⟨LowBandObjective004Delivery1.data, LowBandObjective004Delivery1.checked, LowBandObjective004Delivery1.initial_states⟩
    · exact ⟨LowBandObjective004Delivery2.data, LowBandObjective004Delivery2.checked, LowBandObjective004Delivery2.initial_states⟩
    · exact ⟨LowBandObjective004Delivery3.data, LowBandObjective004Delivery3.checked, LowBandObjective004Delivery3.initial_states⟩
    · exact ⟨LowBandObjective004Delivery4.data, LowBandObjective004Delivery4.checked, LowBandObjective004Delivery4.initial_states⟩
    · exact ⟨LowBandObjective004Delivery5.data, LowBandObjective004Delivery5.checked, LowBandObjective004Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate004
