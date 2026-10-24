import SixTypeObjective68Transfer
import SixTypeObjective68Delivery0
import SixTypeObjective68Delivery1
import SixTypeObjective68Delivery2
import SixTypeObjective68Delivery3
import SixTypeObjective68Delivery4
import SixTypeObjective68Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate68
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern68.pattern := by
  constructor
  · exact ⟨SixTypeObjective68Transfer.data, SixTypeObjective68Transfer.checked, SixTypeObjective68Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective68Delivery0.data, SixTypeObjective68Delivery0.checked, SixTypeObjective68Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective68Delivery1.data, SixTypeObjective68Delivery1.checked, SixTypeObjective68Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective68Delivery2.data, SixTypeObjective68Delivery2.checked, SixTypeObjective68Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective68Delivery3.data, SixTypeObjective68Delivery3.checked, SixTypeObjective68Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective68Delivery4.data, SixTypeObjective68Delivery4.checked, SixTypeObjective68Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective68Delivery5.data, SixTypeObjective68Delivery5.checked, SixTypeObjective68Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate68
