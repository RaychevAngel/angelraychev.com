import SixTypeObjective42Transfer
import SixTypeObjective42Delivery0
import SixTypeObjective42Delivery1
import SixTypeObjective42Delivery2
import SixTypeObjective42Delivery3
import SixTypeObjective42Delivery4
import SixTypeObjective42Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate42
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern42.pattern := by
  constructor
  · exact ⟨SixTypeObjective42Transfer.data, SixTypeObjective42Transfer.checked, SixTypeObjective42Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective42Delivery0.data, SixTypeObjective42Delivery0.checked, SixTypeObjective42Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective42Delivery1.data, SixTypeObjective42Delivery1.checked, SixTypeObjective42Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective42Delivery2.data, SixTypeObjective42Delivery2.checked, SixTypeObjective42Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective42Delivery3.data, SixTypeObjective42Delivery3.checked, SixTypeObjective42Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective42Delivery4.data, SixTypeObjective42Delivery4.checked, SixTypeObjective42Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective42Delivery5.data, SixTypeObjective42Delivery5.checked, SixTypeObjective42Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate42
