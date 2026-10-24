import SixTypeObjective33Transfer
import SixTypeObjective33Delivery0
import SixTypeObjective33Delivery1
import SixTypeObjective33Delivery2
import SixTypeObjective33Delivery3
import SixTypeObjective33Delivery4
import SixTypeObjective33Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate33
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern33.pattern := by
  constructor
  · exact ⟨SixTypeObjective33Transfer.data, SixTypeObjective33Transfer.checked, SixTypeObjective33Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective33Delivery0.data, SixTypeObjective33Delivery0.checked, SixTypeObjective33Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective33Delivery1.data, SixTypeObjective33Delivery1.checked, SixTypeObjective33Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective33Delivery2.data, SixTypeObjective33Delivery2.checked, SixTypeObjective33Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective33Delivery3.data, SixTypeObjective33Delivery3.checked, SixTypeObjective33Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective33Delivery4.data, SixTypeObjective33Delivery4.checked, SixTypeObjective33Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective33Delivery5.data, SixTypeObjective33Delivery5.checked, SixTypeObjective33Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate33
