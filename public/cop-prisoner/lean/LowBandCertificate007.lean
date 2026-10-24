import LowBandObjective007Transfer
import LowBandObjective007Delivery0
import LowBandObjective007Delivery1
import LowBandObjective007Delivery2
import LowBandObjective007Delivery3
import LowBandObjective007Delivery4
import LowBandObjective007Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate007
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern007.pattern := by
  constructor
  · exact ⟨LowBandObjective007Transfer.data, LowBandObjective007Transfer.checked, LowBandObjective007Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective007Delivery0.data, LowBandObjective007Delivery0.checked, LowBandObjective007Delivery0.initial_states⟩
    · exact ⟨LowBandObjective007Delivery1.data, LowBandObjective007Delivery1.checked, LowBandObjective007Delivery1.initial_states⟩
    · exact ⟨LowBandObjective007Delivery2.data, LowBandObjective007Delivery2.checked, LowBandObjective007Delivery2.initial_states⟩
    · exact ⟨LowBandObjective007Delivery3.data, LowBandObjective007Delivery3.checked, LowBandObjective007Delivery3.initial_states⟩
    · exact ⟨LowBandObjective007Delivery4.data, LowBandObjective007Delivery4.checked, LowBandObjective007Delivery4.initial_states⟩
    · exact ⟨LowBandObjective007Delivery5.data, LowBandObjective007Delivery5.checked, LowBandObjective007Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate007
