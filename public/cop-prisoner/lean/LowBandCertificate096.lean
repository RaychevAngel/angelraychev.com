import LowBandObjective096Transfer
import LowBandObjective096Delivery0
import LowBandObjective096Delivery1
import LowBandObjective096Delivery2
import LowBandObjective096Delivery3
import LowBandObjective096Delivery4
import LowBandObjective096Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate096
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern096.pattern := by
  constructor
  · exact ⟨LowBandObjective096Transfer.data, LowBandObjective096Transfer.checked, LowBandObjective096Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective096Delivery0.data, LowBandObjective096Delivery0.checked, LowBandObjective096Delivery0.initial_states⟩
    · exact ⟨LowBandObjective096Delivery1.data, LowBandObjective096Delivery1.checked, LowBandObjective096Delivery1.initial_states⟩
    · exact ⟨LowBandObjective096Delivery2.data, LowBandObjective096Delivery2.checked, LowBandObjective096Delivery2.initial_states⟩
    · exact ⟨LowBandObjective096Delivery3.data, LowBandObjective096Delivery3.checked, LowBandObjective096Delivery3.initial_states⟩
    · exact ⟨LowBandObjective096Delivery4.data, LowBandObjective096Delivery4.checked, LowBandObjective096Delivery4.initial_states⟩
    · exact ⟨LowBandObjective096Delivery5.data, LowBandObjective096Delivery5.checked, LowBandObjective096Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate096
