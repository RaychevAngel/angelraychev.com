import SixTypeObjective10Transfer
import SixTypeObjective10Delivery0
import SixTypeObjective10Delivery1
import SixTypeObjective10Delivery2
import SixTypeObjective10Delivery3
import SixTypeObjective10Delivery4
import SixTypeObjective10Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate10
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern10.pattern := by
  constructor
  · exact ⟨SixTypeObjective10Transfer.data, SixTypeObjective10Transfer.checked, SixTypeObjective10Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective10Delivery0.data, SixTypeObjective10Delivery0.checked, SixTypeObjective10Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective10Delivery1.data, SixTypeObjective10Delivery1.checked, SixTypeObjective10Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective10Delivery2.data, SixTypeObjective10Delivery2.checked, SixTypeObjective10Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective10Delivery3.data, SixTypeObjective10Delivery3.checked, SixTypeObjective10Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective10Delivery4.data, SixTypeObjective10Delivery4.checked, SixTypeObjective10Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective10Delivery5.data, SixTypeObjective10Delivery5.checked, SixTypeObjective10Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate10
