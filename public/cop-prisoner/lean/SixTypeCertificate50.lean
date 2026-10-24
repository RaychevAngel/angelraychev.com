import SixTypeObjective50Transfer
import SixTypeObjective50Delivery0
import SixTypeObjective50Delivery1
import SixTypeObjective50Delivery2
import SixTypeObjective50Delivery3
import SixTypeObjective50Delivery4
import SixTypeObjective50Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate50
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern50.pattern := by
  constructor
  · exact ⟨SixTypeObjective50Transfer.data, SixTypeObjective50Transfer.checked, SixTypeObjective50Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective50Delivery0.data, SixTypeObjective50Delivery0.checked, SixTypeObjective50Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective50Delivery1.data, SixTypeObjective50Delivery1.checked, SixTypeObjective50Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective50Delivery2.data, SixTypeObjective50Delivery2.checked, SixTypeObjective50Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective50Delivery3.data, SixTypeObjective50Delivery3.checked, SixTypeObjective50Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective50Delivery4.data, SixTypeObjective50Delivery4.checked, SixTypeObjective50Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective50Delivery5.data, SixTypeObjective50Delivery5.checked, SixTypeObjective50Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate50
