import LowBandObjective068Transfer
import LowBandObjective068Delivery0
import LowBandObjective068Delivery1
import LowBandObjective068Delivery2
import LowBandObjective068Delivery3
import LowBandObjective068Delivery4
import LowBandObjective068Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate068
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern068.pattern := by
  constructor
  · exact ⟨LowBandObjective068Transfer.data, LowBandObjective068Transfer.checked, LowBandObjective068Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective068Delivery0.data, LowBandObjective068Delivery0.checked, LowBandObjective068Delivery0.initial_states⟩
    · exact ⟨LowBandObjective068Delivery1.data, LowBandObjective068Delivery1.checked, LowBandObjective068Delivery1.initial_states⟩
    · exact ⟨LowBandObjective068Delivery2.data, LowBandObjective068Delivery2.checked, LowBandObjective068Delivery2.initial_states⟩
    · exact ⟨LowBandObjective068Delivery3.data, LowBandObjective068Delivery3.checked, LowBandObjective068Delivery3.initial_states⟩
    · exact ⟨LowBandObjective068Delivery4.data, LowBandObjective068Delivery4.checked, LowBandObjective068Delivery4.initial_states⟩
    · exact ⟨LowBandObjective068Delivery5.data, LowBandObjective068Delivery5.checked, LowBandObjective068Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate068
