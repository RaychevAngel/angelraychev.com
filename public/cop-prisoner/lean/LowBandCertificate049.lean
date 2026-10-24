import LowBandObjective049Transfer
import LowBandObjective049Delivery0
import LowBandObjective049Delivery1
import LowBandObjective049Delivery2
import LowBandObjective049Delivery3
import LowBandObjective049Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate049
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern049.pattern := by
  constructor
  · exact ⟨LowBandObjective049Transfer.data, LowBandObjective049Transfer.checked, LowBandObjective049Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective049Delivery0.data, LowBandObjective049Delivery0.checked, LowBandObjective049Delivery0.initial_states⟩
    · exact ⟨LowBandObjective049Delivery1.data, LowBandObjective049Delivery1.checked, LowBandObjective049Delivery1.initial_states⟩
    · exact ⟨LowBandObjective049Delivery2.data, LowBandObjective049Delivery2.checked, LowBandObjective049Delivery2.initial_states⟩
    · exact ⟨LowBandObjective049Delivery3.data, LowBandObjective049Delivery3.checked, LowBandObjective049Delivery3.initial_states⟩
    · simp [LowBandPattern049.pattern] at present
    · exact ⟨LowBandObjective049Delivery5.data, LowBandObjective049Delivery5.checked, LowBandObjective049Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate049
