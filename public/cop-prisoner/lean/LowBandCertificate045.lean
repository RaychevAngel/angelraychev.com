import LowBandObjective045Transfer
import LowBandObjective045Delivery0
import LowBandObjective045Delivery1
import LowBandObjective045Delivery2
import LowBandObjective045Delivery3
import LowBandObjective045Delivery4
import LowBandObjective045Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate045
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern045.pattern := by
  constructor
  · exact ⟨LowBandObjective045Transfer.data, LowBandObjective045Transfer.checked, LowBandObjective045Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective045Delivery0.data, LowBandObjective045Delivery0.checked, LowBandObjective045Delivery0.initial_states⟩
    · exact ⟨LowBandObjective045Delivery1.data, LowBandObjective045Delivery1.checked, LowBandObjective045Delivery1.initial_states⟩
    · exact ⟨LowBandObjective045Delivery2.data, LowBandObjective045Delivery2.checked, LowBandObjective045Delivery2.initial_states⟩
    · exact ⟨LowBandObjective045Delivery3.data, LowBandObjective045Delivery3.checked, LowBandObjective045Delivery3.initial_states⟩
    · exact ⟨LowBandObjective045Delivery4.data, LowBandObjective045Delivery4.checked, LowBandObjective045Delivery4.initial_states⟩
    · exact ⟨LowBandObjective045Delivery5.data, LowBandObjective045Delivery5.checked, LowBandObjective045Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate045
