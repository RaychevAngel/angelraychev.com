import SixTypeObjective28Transfer
import SixTypeObjective28Delivery0
import SixTypeObjective28Delivery1
import SixTypeObjective28Delivery2
import SixTypeObjective28Delivery3
import SixTypeObjective28Delivery4
import SixTypeObjective28Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate28
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern28.pattern := by
  constructor
  · exact ⟨SixTypeObjective28Transfer.data, SixTypeObjective28Transfer.checked, SixTypeObjective28Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective28Delivery0.data, SixTypeObjective28Delivery0.checked, SixTypeObjective28Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective28Delivery1.data, SixTypeObjective28Delivery1.checked, SixTypeObjective28Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective28Delivery2.data, SixTypeObjective28Delivery2.checked, SixTypeObjective28Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective28Delivery3.data, SixTypeObjective28Delivery3.checked, SixTypeObjective28Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective28Delivery4.data, SixTypeObjective28Delivery4.checked, SixTypeObjective28Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective28Delivery5.data, SixTypeObjective28Delivery5.checked, SixTypeObjective28Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate28
