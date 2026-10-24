import SixTypeObjective47Transfer
import SixTypeObjective47Delivery0
import SixTypeObjective47Delivery1
import SixTypeObjective47Delivery2
import SixTypeObjective47Delivery3
import SixTypeObjective47Delivery4
import SixTypeObjective47Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate47
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern47.pattern := by
  constructor
  · exact ⟨SixTypeObjective47Transfer.data, SixTypeObjective47Transfer.checked, SixTypeObjective47Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective47Delivery0.data, SixTypeObjective47Delivery0.checked, SixTypeObjective47Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective47Delivery1.data, SixTypeObjective47Delivery1.checked, SixTypeObjective47Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective47Delivery2.data, SixTypeObjective47Delivery2.checked, SixTypeObjective47Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective47Delivery3.data, SixTypeObjective47Delivery3.checked, SixTypeObjective47Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective47Delivery4.data, SixTypeObjective47Delivery4.checked, SixTypeObjective47Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective47Delivery5.data, SixTypeObjective47Delivery5.checked, SixTypeObjective47Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate47
