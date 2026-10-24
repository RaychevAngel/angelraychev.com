import SixTypeObjective25Transfer
import SixTypeObjective25Delivery0
import SixTypeObjective25Delivery1
import SixTypeObjective25Delivery2
import SixTypeObjective25Delivery3
import SixTypeObjective25Delivery4
import SixTypeObjective25Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate25
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern25.pattern := by
  constructor
  · exact ⟨SixTypeObjective25Transfer.data, SixTypeObjective25Transfer.checked, SixTypeObjective25Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective25Delivery0.data, SixTypeObjective25Delivery0.checked, SixTypeObjective25Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective25Delivery1.data, SixTypeObjective25Delivery1.checked, SixTypeObjective25Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective25Delivery2.data, SixTypeObjective25Delivery2.checked, SixTypeObjective25Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective25Delivery3.data, SixTypeObjective25Delivery3.checked, SixTypeObjective25Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective25Delivery4.data, SixTypeObjective25Delivery4.checked, SixTypeObjective25Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective25Delivery5.data, SixTypeObjective25Delivery5.checked, SixTypeObjective25Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate25
