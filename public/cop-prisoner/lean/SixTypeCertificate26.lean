import SixTypeObjective26Transfer
import SixTypeObjective26Delivery0
import SixTypeObjective26Delivery1
import SixTypeObjective26Delivery2
import SixTypeObjective26Delivery3
import SixTypeObjective26Delivery4
import SixTypeObjective26Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate26
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern26.pattern := by
  constructor
  · exact ⟨SixTypeObjective26Transfer.data, SixTypeObjective26Transfer.checked, SixTypeObjective26Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective26Delivery0.data, SixTypeObjective26Delivery0.checked, SixTypeObjective26Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective26Delivery1.data, SixTypeObjective26Delivery1.checked, SixTypeObjective26Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective26Delivery2.data, SixTypeObjective26Delivery2.checked, SixTypeObjective26Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective26Delivery3.data, SixTypeObjective26Delivery3.checked, SixTypeObjective26Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective26Delivery4.data, SixTypeObjective26Delivery4.checked, SixTypeObjective26Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective26Delivery5.data, SixTypeObjective26Delivery5.checked, SixTypeObjective26Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate26
