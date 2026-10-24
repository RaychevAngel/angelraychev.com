import LowBandObjective012Transfer
import LowBandObjective012Delivery0
import LowBandObjective012Delivery1
import LowBandObjective012Delivery2
import LowBandObjective012Delivery3
import LowBandObjective012Delivery4
import LowBandObjective012Delivery5
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificate012
open LocalArena LocalArenaRows LowBandLocal
theorem checked : Certificates LowBandPattern012.pattern := by
  constructor
  · exact ⟨LowBandObjective012Transfer.data, LowBandObjective012Transfer.checked, LowBandObjective012Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨LowBandObjective012Delivery0.data, LowBandObjective012Delivery0.checked, LowBandObjective012Delivery0.initial_states⟩
    · exact ⟨LowBandObjective012Delivery1.data, LowBandObjective012Delivery1.checked, LowBandObjective012Delivery1.initial_states⟩
    · exact ⟨LowBandObjective012Delivery2.data, LowBandObjective012Delivery2.checked, LowBandObjective012Delivery2.initial_states⟩
    · exact ⟨LowBandObjective012Delivery3.data, LowBandObjective012Delivery3.checked, LowBandObjective012Delivery3.initial_states⟩
    · exact ⟨LowBandObjective012Delivery4.data, LowBandObjective012Delivery4.checked, LowBandObjective012Delivery4.initial_states⟩
    · exact ⟨LowBandObjective012Delivery5.data, LowBandObjective012Delivery5.checked, LowBandObjective012Delivery5.initial_states⟩
#print axioms checked
end Delivery.LowBandCertificate012
