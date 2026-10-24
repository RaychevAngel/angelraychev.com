import SixTypeObjective38Transfer
import SixTypeObjective38Delivery0
import SixTypeObjective38Delivery1
import SixTypeObjective38Delivery2
import SixTypeObjective38Delivery3
import SixTypeObjective38Delivery4
import SixTypeObjective38Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate38
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern38.pattern := by
  constructor
  · exact ⟨SixTypeObjective38Transfer.data, SixTypeObjective38Transfer.checked, SixTypeObjective38Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective38Delivery0.data, SixTypeObjective38Delivery0.checked, SixTypeObjective38Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective38Delivery1.data, SixTypeObjective38Delivery1.checked, SixTypeObjective38Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective38Delivery2.data, SixTypeObjective38Delivery2.checked, SixTypeObjective38Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective38Delivery3.data, SixTypeObjective38Delivery3.checked, SixTypeObjective38Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective38Delivery4.data, SixTypeObjective38Delivery4.checked, SixTypeObjective38Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective38Delivery5.data, SixTypeObjective38Delivery5.checked, SixTypeObjective38Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate38
