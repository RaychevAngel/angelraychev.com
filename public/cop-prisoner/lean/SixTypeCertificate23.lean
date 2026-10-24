import SixTypeObjective23Transfer
import SixTypeObjective23Delivery0
import SixTypeObjective23Delivery1
import SixTypeObjective23Delivery2
import SixTypeObjective23Delivery3
import SixTypeObjective23Delivery4
import SixTypeObjective23Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate23
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern23.pattern := by
  constructor
  · exact ⟨SixTypeObjective23Transfer.data, SixTypeObjective23Transfer.checked, SixTypeObjective23Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective23Delivery0.data, SixTypeObjective23Delivery0.checked, SixTypeObjective23Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective23Delivery1.data, SixTypeObjective23Delivery1.checked, SixTypeObjective23Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective23Delivery2.data, SixTypeObjective23Delivery2.checked, SixTypeObjective23Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective23Delivery3.data, SixTypeObjective23Delivery3.checked, SixTypeObjective23Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective23Delivery4.data, SixTypeObjective23Delivery4.checked, SixTypeObjective23Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective23Delivery5.data, SixTypeObjective23Delivery5.checked, SixTypeObjective23Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate23
