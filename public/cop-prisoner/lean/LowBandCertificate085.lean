import LowBandObjective085Transfer
import LowBandObjective085Delivery0
import LowBandObjective085Delivery1
import LowBandObjective085Delivery2
import LowBandObjective085Delivery3
import LowBandObjective085Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate085
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern085.pattern := by
  constructor
  · exact ⟨LowBandObjective085Transfer.data, LowBandObjective085Transfer.checked, LowBandObjective085Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective085Delivery0.data, LowBandObjective085Delivery0.checked, LowBandObjective085Delivery0.initial_states⟩
    · exact ⟨LowBandObjective085Delivery1.data, LowBandObjective085Delivery1.checked, LowBandObjective085Delivery1.initial_states⟩
    · exact ⟨LowBandObjective085Delivery2.data, LowBandObjective085Delivery2.checked, LowBandObjective085Delivery2.initial_states⟩
    · exact ⟨LowBandObjective085Delivery3.data, LowBandObjective085Delivery3.checked, LowBandObjective085Delivery3.initial_states⟩
    · simp [LowBandPattern085.pattern] at present
    · exact ⟨LowBandObjective085Delivery5.data, LowBandObjective085Delivery5.checked, LowBandObjective085Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate085
