import SixTypeObjective00Transfer
import SixTypeObjective00Delivery0
import SixTypeObjective00Delivery1
import SixTypeObjective00Delivery2
import SixTypeObjective00Delivery3
import SixTypeObjective00Delivery4
import SixTypeObjective00Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate00
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern00.pattern := by
  constructor
  · exact ⟨SixTypeObjective00Transfer.data, SixTypeObjective00Transfer.checked, SixTypeObjective00Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective00Delivery0.data, SixTypeObjective00Delivery0.checked, SixTypeObjective00Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective00Delivery1.data, SixTypeObjective00Delivery1.checked, SixTypeObjective00Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective00Delivery2.data, SixTypeObjective00Delivery2.checked, SixTypeObjective00Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective00Delivery3.data, SixTypeObjective00Delivery3.checked, SixTypeObjective00Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective00Delivery4.data, SixTypeObjective00Delivery4.checked, SixTypeObjective00Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective00Delivery5.data, SixTypeObjective00Delivery5.checked, SixTypeObjective00Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate00
