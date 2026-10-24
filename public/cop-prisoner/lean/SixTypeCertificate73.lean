import SixTypeObjective73Transfer
import SixTypeObjective73Delivery0
import SixTypeObjective73Delivery1
import SixTypeObjective73Delivery2
import SixTypeObjective73Delivery3
import SixTypeObjective73Delivery4
import SixTypeObjective73Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate73
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern73.pattern := by
  constructor
  · exact ⟨SixTypeObjective73Transfer.data, SixTypeObjective73Transfer.checked, SixTypeObjective73Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective73Delivery0.data, SixTypeObjective73Delivery0.checked, SixTypeObjective73Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective73Delivery1.data, SixTypeObjective73Delivery1.checked, SixTypeObjective73Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective73Delivery2.data, SixTypeObjective73Delivery2.checked, SixTypeObjective73Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective73Delivery3.data, SixTypeObjective73Delivery3.checked, SixTypeObjective73Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective73Delivery4.data, SixTypeObjective73Delivery4.checked, SixTypeObjective73Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective73Delivery5.data, SixTypeObjective73Delivery5.checked, SixTypeObjective73Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate73
