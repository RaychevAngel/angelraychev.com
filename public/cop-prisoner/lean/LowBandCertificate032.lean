import LowBandObjective032Transfer
import LowBandObjective032Delivery0
import LowBandObjective032Delivery1
import LowBandObjective032Delivery2
import LowBandObjective032Delivery3
import LowBandObjective032Delivery4
import LowBandObjective032Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate032
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern032.pattern := by
  constructor
  · exact ⟨LowBandObjective032Transfer.data, LowBandObjective032Transfer.checked, LowBandObjective032Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective032Delivery0.data, LowBandObjective032Delivery0.checked, LowBandObjective032Delivery0.initial_states⟩
    · exact ⟨LowBandObjective032Delivery1.data, LowBandObjective032Delivery1.checked, LowBandObjective032Delivery1.initial_states⟩
    · exact ⟨LowBandObjective032Delivery2.data, LowBandObjective032Delivery2.checked, LowBandObjective032Delivery2.initial_states⟩
    · exact ⟨LowBandObjective032Delivery3.data, LowBandObjective032Delivery3.checked, LowBandObjective032Delivery3.initial_states⟩
    · exact ⟨LowBandObjective032Delivery4.data, LowBandObjective032Delivery4.checked, LowBandObjective032Delivery4.initial_states⟩
    · exact ⟨LowBandObjective032Delivery5.data, LowBandObjective032Delivery5.checked, LowBandObjective032Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate032
