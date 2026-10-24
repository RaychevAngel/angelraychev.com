import LowBandObjective026Transfer
import LowBandObjective026Delivery0
import LowBandObjective026Delivery1
import LowBandObjective026Delivery2
import LowBandObjective026Delivery3
import LowBandObjective026Delivery4
import LowBandObjective026Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate026
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern026.pattern := by
  constructor
  · exact ⟨LowBandObjective026Transfer.data, LowBandObjective026Transfer.checked, LowBandObjective026Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective026Delivery0.data, LowBandObjective026Delivery0.checked, LowBandObjective026Delivery0.initial_states⟩
    · exact ⟨LowBandObjective026Delivery1.data, LowBandObjective026Delivery1.checked, LowBandObjective026Delivery1.initial_states⟩
    · exact ⟨LowBandObjective026Delivery2.data, LowBandObjective026Delivery2.checked, LowBandObjective026Delivery2.initial_states⟩
    · exact ⟨LowBandObjective026Delivery3.data, LowBandObjective026Delivery3.checked, LowBandObjective026Delivery3.initial_states⟩
    · exact ⟨LowBandObjective026Delivery4.data, LowBandObjective026Delivery4.checked, LowBandObjective026Delivery4.initial_states⟩
    · exact ⟨LowBandObjective026Delivery5.data, LowBandObjective026Delivery5.checked, LowBandObjective026Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate026
