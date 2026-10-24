import SixTypeObjective46Transfer
import SixTypeObjective46Delivery0
import SixTypeObjective46Delivery1
import SixTypeObjective46Delivery2
import SixTypeObjective46Delivery3
import SixTypeObjective46Delivery4
import SixTypeObjective46Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate46
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern46.pattern := by
  constructor
  · exact ⟨SixTypeObjective46Transfer.data, SixTypeObjective46Transfer.checked, SixTypeObjective46Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective46Delivery0.data, SixTypeObjective46Delivery0.checked, SixTypeObjective46Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective46Delivery1.data, SixTypeObjective46Delivery1.checked, SixTypeObjective46Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective46Delivery2.data, SixTypeObjective46Delivery2.checked, SixTypeObjective46Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective46Delivery3.data, SixTypeObjective46Delivery3.checked, SixTypeObjective46Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective46Delivery4.data, SixTypeObjective46Delivery4.checked, SixTypeObjective46Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective46Delivery5.data, SixTypeObjective46Delivery5.checked, SixTypeObjective46Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate46
