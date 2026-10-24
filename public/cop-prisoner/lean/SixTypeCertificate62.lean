import SixTypeObjective62Transfer
import SixTypeObjective62Delivery0
import SixTypeObjective62Delivery1
import SixTypeObjective62Delivery2
import SixTypeObjective62Delivery3
import SixTypeObjective62Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate62
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern62.pattern := by
  constructor
  · exact ⟨SixTypeObjective62Transfer.data, SixTypeObjective62Transfer.checked, SixTypeObjective62Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective62Delivery0.data, SixTypeObjective62Delivery0.checked, SixTypeObjective62Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective62Delivery1.data, SixTypeObjective62Delivery1.checked, SixTypeObjective62Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective62Delivery2.data, SixTypeObjective62Delivery2.checked, SixTypeObjective62Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective62Delivery3.data, SixTypeObjective62Delivery3.checked, SixTypeObjective62Delivery3.initial_states⟩
    · simp [SixTypePattern62.pattern] at present
    · exact ⟨SixTypeObjective62Delivery5.data, SixTypeObjective62Delivery5.checked, SixTypeObjective62Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate62
