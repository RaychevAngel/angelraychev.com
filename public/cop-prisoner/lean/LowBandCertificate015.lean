import LowBandObjective015Transfer
import LowBandObjective015Delivery0
import LowBandObjective015Delivery1
import LowBandObjective015Delivery2
import LowBandObjective015Delivery3
import LowBandObjective015Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate015
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern015.pattern := by
  constructor
  · exact ⟨LowBandObjective015Transfer.data, LowBandObjective015Transfer.checked, LowBandObjective015Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective015Delivery0.data, LowBandObjective015Delivery0.checked, LowBandObjective015Delivery0.initial_states⟩
    · exact ⟨LowBandObjective015Delivery1.data, LowBandObjective015Delivery1.checked, LowBandObjective015Delivery1.initial_states⟩
    · exact ⟨LowBandObjective015Delivery2.data, LowBandObjective015Delivery2.checked, LowBandObjective015Delivery2.initial_states⟩
    · exact ⟨LowBandObjective015Delivery3.data, LowBandObjective015Delivery3.checked, LowBandObjective015Delivery3.initial_states⟩
    · simp [LowBandPattern015.pattern] at present
    · exact ⟨LowBandObjective015Delivery5.data, LowBandObjective015Delivery5.checked, LowBandObjective015Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate015
