import SixTypeObjective64Transfer
import SixTypeObjective64Delivery0
import SixTypeObjective64Delivery1
import SixTypeObjective64Delivery2
import SixTypeObjective64Delivery3
import SixTypeObjective64Delivery4
import SixTypeObjective64Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate64
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern64.pattern := by
  constructor
  · exact ⟨SixTypeObjective64Transfer.data, SixTypeObjective64Transfer.checked, SixTypeObjective64Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective64Delivery0.data, SixTypeObjective64Delivery0.checked, SixTypeObjective64Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective64Delivery1.data, SixTypeObjective64Delivery1.checked, SixTypeObjective64Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective64Delivery2.data, SixTypeObjective64Delivery2.checked, SixTypeObjective64Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective64Delivery3.data, SixTypeObjective64Delivery3.checked, SixTypeObjective64Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective64Delivery4.data, SixTypeObjective64Delivery4.checked, SixTypeObjective64Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective64Delivery5.data, SixTypeObjective64Delivery5.checked, SixTypeObjective64Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate64
