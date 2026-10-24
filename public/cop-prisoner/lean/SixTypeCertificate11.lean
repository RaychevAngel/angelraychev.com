import SixTypeObjective11Transfer
import SixTypeObjective11Delivery0
import SixTypeObjective11Delivery1
import SixTypeObjective11Delivery2
import SixTypeObjective11Delivery3
import SixTypeObjective11Delivery4
import SixTypeObjective11Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate11
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern11.pattern := by
  constructor
  · exact ⟨SixTypeObjective11Transfer.data, SixTypeObjective11Transfer.checked, SixTypeObjective11Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective11Delivery0.data, SixTypeObjective11Delivery0.checked, SixTypeObjective11Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective11Delivery1.data, SixTypeObjective11Delivery1.checked, SixTypeObjective11Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective11Delivery2.data, SixTypeObjective11Delivery2.checked, SixTypeObjective11Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective11Delivery3.data, SixTypeObjective11Delivery3.checked, SixTypeObjective11Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective11Delivery4.data, SixTypeObjective11Delivery4.checked, SixTypeObjective11Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective11Delivery5.data, SixTypeObjective11Delivery5.checked, SixTypeObjective11Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate11
