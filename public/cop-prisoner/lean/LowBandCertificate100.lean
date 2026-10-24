import LowBandObjective100Transfer
import LowBandObjective100Delivery0
import LowBandObjective100Delivery1
import LowBandObjective100Delivery2
import LowBandObjective100Delivery3
import LowBandObjective100Delivery4
import LowBandObjective100Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate100
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern100.pattern := by
  constructor
  · exact ⟨LowBandObjective100Transfer.data, LowBandObjective100Transfer.checked, LowBandObjective100Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective100Delivery0.data, LowBandObjective100Delivery0.checked, LowBandObjective100Delivery0.initial_states⟩
    · exact ⟨LowBandObjective100Delivery1.data, LowBandObjective100Delivery1.checked, LowBandObjective100Delivery1.initial_states⟩
    · exact ⟨LowBandObjective100Delivery2.data, LowBandObjective100Delivery2.checked, LowBandObjective100Delivery2.initial_states⟩
    · exact ⟨LowBandObjective100Delivery3.data, LowBandObjective100Delivery3.checked, LowBandObjective100Delivery3.initial_states⟩
    · exact ⟨LowBandObjective100Delivery4.data, LowBandObjective100Delivery4.checked, LowBandObjective100Delivery4.initial_states⟩
    · exact ⟨LowBandObjective100Delivery5.data, LowBandObjective100Delivery5.checked, LowBandObjective100Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate100
