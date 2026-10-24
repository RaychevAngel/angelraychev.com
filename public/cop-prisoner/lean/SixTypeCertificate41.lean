import SixTypeObjective41Transfer
import SixTypeObjective41Delivery0
import SixTypeObjective41Delivery1
import SixTypeObjective41Delivery2
import SixTypeObjective41Delivery3
import SixTypeObjective41Delivery4
import SixTypeObjective41Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate41
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern41.pattern := by
  constructor
  · exact ⟨SixTypeObjective41Transfer.data, SixTypeObjective41Transfer.checked, SixTypeObjective41Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective41Delivery0.data, SixTypeObjective41Delivery0.checked, SixTypeObjective41Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective41Delivery1.data, SixTypeObjective41Delivery1.checked, SixTypeObjective41Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective41Delivery2.data, SixTypeObjective41Delivery2.checked, SixTypeObjective41Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective41Delivery3.data, SixTypeObjective41Delivery3.checked, SixTypeObjective41Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective41Delivery4.data, SixTypeObjective41Delivery4.checked, SixTypeObjective41Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective41Delivery5.data, SixTypeObjective41Delivery5.checked, SixTypeObjective41Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate41
