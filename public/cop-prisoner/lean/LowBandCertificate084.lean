import LowBandObjective084Transfer
import LowBandObjective084Delivery0
import LowBandObjective084Delivery1
import LowBandObjective084Delivery2
import LowBandObjective084Delivery3
import LowBandObjective084Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate084
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern084.pattern := by
  constructor
  · exact ⟨LowBandObjective084Transfer.data, LowBandObjective084Transfer.checked, LowBandObjective084Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective084Delivery0.data, LowBandObjective084Delivery0.checked, LowBandObjective084Delivery0.initial_states⟩
    · exact ⟨LowBandObjective084Delivery1.data, LowBandObjective084Delivery1.checked, LowBandObjective084Delivery1.initial_states⟩
    · exact ⟨LowBandObjective084Delivery2.data, LowBandObjective084Delivery2.checked, LowBandObjective084Delivery2.initial_states⟩
    · exact ⟨LowBandObjective084Delivery3.data, LowBandObjective084Delivery3.checked, LowBandObjective084Delivery3.initial_states⟩
    · simp [LowBandPattern084.pattern] at present
    · exact ⟨LowBandObjective084Delivery5.data, LowBandObjective084Delivery5.checked, LowBandObjective084Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate084
