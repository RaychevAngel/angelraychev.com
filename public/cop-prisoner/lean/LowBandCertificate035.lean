import LowBandObjective035Transfer
import LowBandObjective035Delivery0
import LowBandObjective035Delivery1
import LowBandObjective035Delivery2
import LowBandObjective035Delivery3
import LowBandObjective035Delivery4
import LowBandObjective035Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate035
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern035.pattern := by
  constructor
  · exact ⟨LowBandObjective035Transfer.data, LowBandObjective035Transfer.checked, LowBandObjective035Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective035Delivery0.data, LowBandObjective035Delivery0.checked, LowBandObjective035Delivery0.initial_states⟩
    · exact ⟨LowBandObjective035Delivery1.data, LowBandObjective035Delivery1.checked, LowBandObjective035Delivery1.initial_states⟩
    · exact ⟨LowBandObjective035Delivery2.data, LowBandObjective035Delivery2.checked, LowBandObjective035Delivery2.initial_states⟩
    · exact ⟨LowBandObjective035Delivery3.data, LowBandObjective035Delivery3.checked, LowBandObjective035Delivery3.initial_states⟩
    · exact ⟨LowBandObjective035Delivery4.data, LowBandObjective035Delivery4.checked, LowBandObjective035Delivery4.initial_states⟩
    · exact ⟨LowBandObjective035Delivery5.data, LowBandObjective035Delivery5.checked, LowBandObjective035Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate035
