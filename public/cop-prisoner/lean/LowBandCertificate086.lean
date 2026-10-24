import LowBandObjective086Transfer
import LowBandObjective086Delivery0
import LowBandObjective086Delivery1
import LowBandObjective086Delivery2
import LowBandObjective086Delivery3
import LowBandObjective086Delivery4
import LowBandObjective086Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate086
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern086.pattern := by
  constructor
  · exact ⟨LowBandObjective086Transfer.data, LowBandObjective086Transfer.checked, LowBandObjective086Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective086Delivery0.data, LowBandObjective086Delivery0.checked, LowBandObjective086Delivery0.initial_states⟩
    · exact ⟨LowBandObjective086Delivery1.data, LowBandObjective086Delivery1.checked, LowBandObjective086Delivery1.initial_states⟩
    · exact ⟨LowBandObjective086Delivery2.data, LowBandObjective086Delivery2.checked, LowBandObjective086Delivery2.initial_states⟩
    · exact ⟨LowBandObjective086Delivery3.data, LowBandObjective086Delivery3.checked, LowBandObjective086Delivery3.initial_states⟩
    · exact ⟨LowBandObjective086Delivery4.data, LowBandObjective086Delivery4.checked, LowBandObjective086Delivery4.initial_states⟩
    · exact ⟨LowBandObjective086Delivery5.data, LowBandObjective086Delivery5.checked, LowBandObjective086Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate086
