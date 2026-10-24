import LowBandObjective072Transfer
import LowBandObjective072Delivery0
import LowBandObjective072Delivery1
import LowBandObjective072Delivery2
import LowBandObjective072Delivery3
import LowBandObjective072Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate072
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern072.pattern := by
  constructor
  · exact ⟨LowBandObjective072Transfer.data, LowBandObjective072Transfer.checked, LowBandObjective072Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective072Delivery0.data, LowBandObjective072Delivery0.checked, LowBandObjective072Delivery0.initial_states⟩
    · exact ⟨LowBandObjective072Delivery1.data, LowBandObjective072Delivery1.checked, LowBandObjective072Delivery1.initial_states⟩
    · exact ⟨LowBandObjective072Delivery2.data, LowBandObjective072Delivery2.checked, LowBandObjective072Delivery2.initial_states⟩
    · exact ⟨LowBandObjective072Delivery3.data, LowBandObjective072Delivery3.checked, LowBandObjective072Delivery3.initial_states⟩
    · simp [LowBandPattern072.pattern] at present
    · exact ⟨LowBandObjective072Delivery5.data, LowBandObjective072Delivery5.checked, LowBandObjective072Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate072
