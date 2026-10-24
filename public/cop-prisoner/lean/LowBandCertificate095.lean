import LowBandObjective095Transfer
import LowBandObjective095Delivery0
import LowBandObjective095Delivery1
import LowBandObjective095Delivery2
import LowBandObjective095Delivery3
import LowBandObjective095Delivery4
import LowBandObjective095Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate095
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern095.pattern := by
  constructor
  · exact ⟨LowBandObjective095Transfer.data, LowBandObjective095Transfer.checked, LowBandObjective095Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective095Delivery0.data, LowBandObjective095Delivery0.checked, LowBandObjective095Delivery0.initial_states⟩
    · exact ⟨LowBandObjective095Delivery1.data, LowBandObjective095Delivery1.checked, LowBandObjective095Delivery1.initial_states⟩
    · exact ⟨LowBandObjective095Delivery2.data, LowBandObjective095Delivery2.checked, LowBandObjective095Delivery2.initial_states⟩
    · exact ⟨LowBandObjective095Delivery3.data, LowBandObjective095Delivery3.checked, LowBandObjective095Delivery3.initial_states⟩
    · exact ⟨LowBandObjective095Delivery4.data, LowBandObjective095Delivery4.checked, LowBandObjective095Delivery4.initial_states⟩
    · exact ⟨LowBandObjective095Delivery5.data, LowBandObjective095Delivery5.checked, LowBandObjective095Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate095
