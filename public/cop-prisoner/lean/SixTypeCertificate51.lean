import SixTypeObjective51Transfer
import SixTypeObjective51Delivery0
import SixTypeObjective51Delivery1
import SixTypeObjective51Delivery2
import SixTypeObjective51Delivery3
import SixTypeObjective51Delivery4
import SixTypeObjective51Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate51
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern51.pattern := by
  constructor
  · exact ⟨SixTypeObjective51Transfer.data, SixTypeObjective51Transfer.checked, SixTypeObjective51Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective51Delivery0.data, SixTypeObjective51Delivery0.checked, SixTypeObjective51Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective51Delivery1.data, SixTypeObjective51Delivery1.checked, SixTypeObjective51Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective51Delivery2.data, SixTypeObjective51Delivery2.checked, SixTypeObjective51Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective51Delivery3.data, SixTypeObjective51Delivery3.checked, SixTypeObjective51Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective51Delivery4.data, SixTypeObjective51Delivery4.checked, SixTypeObjective51Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective51Delivery5.data, SixTypeObjective51Delivery5.checked, SixTypeObjective51Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate51
