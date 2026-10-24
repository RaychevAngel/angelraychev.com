import LowBandObjective034Transfer
import LowBandObjective034Delivery0
import LowBandObjective034Delivery1
import LowBandObjective034Delivery2
import LowBandObjective034Delivery3
import LowBandObjective034Delivery4
import LowBandObjective034Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate034
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern034.pattern := by
  constructor
  · exact ⟨LowBandObjective034Transfer.data, LowBandObjective034Transfer.checked, LowBandObjective034Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective034Delivery0.data, LowBandObjective034Delivery0.checked, LowBandObjective034Delivery0.initial_states⟩
    · exact ⟨LowBandObjective034Delivery1.data, LowBandObjective034Delivery1.checked, LowBandObjective034Delivery1.initial_states⟩
    · exact ⟨LowBandObjective034Delivery2.data, LowBandObjective034Delivery2.checked, LowBandObjective034Delivery2.initial_states⟩
    · exact ⟨LowBandObjective034Delivery3.data, LowBandObjective034Delivery3.checked, LowBandObjective034Delivery3.initial_states⟩
    · exact ⟨LowBandObjective034Delivery4.data, LowBandObjective034Delivery4.checked, LowBandObjective034Delivery4.initial_states⟩
    · exact ⟨LowBandObjective034Delivery5.data, LowBandObjective034Delivery5.checked, LowBandObjective034Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate034
