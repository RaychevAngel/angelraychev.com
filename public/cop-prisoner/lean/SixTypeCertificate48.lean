import SixTypeObjective48Transfer
import SixTypeObjective48Delivery0
import SixTypeObjective48Delivery1
import SixTypeObjective48Delivery2
import SixTypeObjective48Delivery3
import SixTypeObjective48Delivery4
import SixTypeObjective48Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate48
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern48.pattern := by
  constructor
  · exact ⟨SixTypeObjective48Transfer.data, SixTypeObjective48Transfer.checked, SixTypeObjective48Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective48Delivery0.data, SixTypeObjective48Delivery0.checked, SixTypeObjective48Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective48Delivery1.data, SixTypeObjective48Delivery1.checked, SixTypeObjective48Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective48Delivery2.data, SixTypeObjective48Delivery2.checked, SixTypeObjective48Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective48Delivery3.data, SixTypeObjective48Delivery3.checked, SixTypeObjective48Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective48Delivery4.data, SixTypeObjective48Delivery4.checked, SixTypeObjective48Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective48Delivery5.data, SixTypeObjective48Delivery5.checked, SixTypeObjective48Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate48
