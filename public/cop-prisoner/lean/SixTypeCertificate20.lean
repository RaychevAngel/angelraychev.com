import SixTypeObjective20Transfer
import SixTypeObjective20Delivery0
import SixTypeObjective20Delivery1
import SixTypeObjective20Delivery2
import SixTypeObjective20Delivery3
import SixTypeObjective20Delivery4
import SixTypeObjective20Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate20
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern20.pattern := by
  constructor
  · exact ⟨SixTypeObjective20Transfer.data, SixTypeObjective20Transfer.checked, SixTypeObjective20Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective20Delivery0.data, SixTypeObjective20Delivery0.checked, SixTypeObjective20Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective20Delivery1.data, SixTypeObjective20Delivery1.checked, SixTypeObjective20Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective20Delivery2.data, SixTypeObjective20Delivery2.checked, SixTypeObjective20Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective20Delivery3.data, SixTypeObjective20Delivery3.checked, SixTypeObjective20Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective20Delivery4.data, SixTypeObjective20Delivery4.checked, SixTypeObjective20Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective20Delivery5.data, SixTypeObjective20Delivery5.checked, SixTypeObjective20Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate20
