import SixTypeObjective80Transfer
import SixTypeObjective80Delivery0
import SixTypeObjective80Delivery1
import SixTypeObjective80Delivery2
import SixTypeObjective80Delivery3
import SixTypeObjective80Delivery4
import SixTypeObjective80Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate80
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern80.pattern := by
  constructor
  · exact ⟨SixTypeObjective80Transfer.data, SixTypeObjective80Transfer.checked, SixTypeObjective80Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective80Delivery0.data, SixTypeObjective80Delivery0.checked, SixTypeObjective80Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective80Delivery1.data, SixTypeObjective80Delivery1.checked, SixTypeObjective80Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective80Delivery2.data, SixTypeObjective80Delivery2.checked, SixTypeObjective80Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective80Delivery3.data, SixTypeObjective80Delivery3.checked, SixTypeObjective80Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective80Delivery4.data, SixTypeObjective80Delivery4.checked, SixTypeObjective80Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective80Delivery5.data, SixTypeObjective80Delivery5.checked, SixTypeObjective80Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate80
