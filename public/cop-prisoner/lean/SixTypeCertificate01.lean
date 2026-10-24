import SixTypeObjective01Transfer
import SixTypeObjective01Delivery0
import SixTypeObjective01Delivery1
import SixTypeObjective01Delivery2
import SixTypeObjective01Delivery3
import SixTypeObjective01Delivery4
import SixTypeObjective01Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate01
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern01.pattern := by
  constructor
  · exact ⟨SixTypeObjective01Transfer.data, SixTypeObjective01Transfer.checked, SixTypeObjective01Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective01Delivery0.data, SixTypeObjective01Delivery0.checked, SixTypeObjective01Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective01Delivery1.data, SixTypeObjective01Delivery1.checked, SixTypeObjective01Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective01Delivery2.data, SixTypeObjective01Delivery2.checked, SixTypeObjective01Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective01Delivery3.data, SixTypeObjective01Delivery3.checked, SixTypeObjective01Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective01Delivery4.data, SixTypeObjective01Delivery4.checked, SixTypeObjective01Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective01Delivery5.data, SixTypeObjective01Delivery5.checked, SixTypeObjective01Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate01
