import LowBandObjective077Transfer
import LowBandObjective077Delivery0
import LowBandObjective077Delivery1
import LowBandObjective077Delivery2
import LowBandObjective077Delivery3
import LowBandObjective077Delivery4
import LowBandObjective077Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate077
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern077.pattern := by
  constructor
  · exact ⟨LowBandObjective077Transfer.data, LowBandObjective077Transfer.checked, LowBandObjective077Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective077Delivery0.data, LowBandObjective077Delivery0.checked, LowBandObjective077Delivery0.initial_states⟩
    · exact ⟨LowBandObjective077Delivery1.data, LowBandObjective077Delivery1.checked, LowBandObjective077Delivery1.initial_states⟩
    · exact ⟨LowBandObjective077Delivery2.data, LowBandObjective077Delivery2.checked, LowBandObjective077Delivery2.initial_states⟩
    · exact ⟨LowBandObjective077Delivery3.data, LowBandObjective077Delivery3.checked, LowBandObjective077Delivery3.initial_states⟩
    · exact ⟨LowBandObjective077Delivery4.data, LowBandObjective077Delivery4.checked, LowBandObjective077Delivery4.initial_states⟩
    · exact ⟨LowBandObjective077Delivery5.data, LowBandObjective077Delivery5.checked, LowBandObjective077Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate077
