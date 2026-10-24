import LowBandObjective074Transfer
import LowBandObjective074Delivery0
import LowBandObjective074Delivery1
import LowBandObjective074Delivery2
import LowBandObjective074Delivery3
import LowBandObjective074Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate074
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern074.pattern := by
  constructor
  · exact ⟨LowBandObjective074Transfer.data, LowBandObjective074Transfer.checked, LowBandObjective074Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective074Delivery0.data, LowBandObjective074Delivery0.checked, LowBandObjective074Delivery0.initial_states⟩
    · exact ⟨LowBandObjective074Delivery1.data, LowBandObjective074Delivery1.checked, LowBandObjective074Delivery1.initial_states⟩
    · exact ⟨LowBandObjective074Delivery2.data, LowBandObjective074Delivery2.checked, LowBandObjective074Delivery2.initial_states⟩
    · exact ⟨LowBandObjective074Delivery3.data, LowBandObjective074Delivery3.checked, LowBandObjective074Delivery3.initial_states⟩
    · simp [LowBandPattern074.pattern] at present
    · exact ⟨LowBandObjective074Delivery5.data, LowBandObjective074Delivery5.checked, LowBandObjective074Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate074
