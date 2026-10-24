import SixTypeObjective77Transfer
import SixTypeObjective77Delivery0
import SixTypeObjective77Delivery1
import SixTypeObjective77Delivery2
import SixTypeObjective77Delivery3
import SixTypeObjective77Delivery4
import SixTypeObjective77Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate77
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern77.pattern := by
  constructor
  · exact ⟨SixTypeObjective77Transfer.data, SixTypeObjective77Transfer.checked, SixTypeObjective77Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective77Delivery0.data, SixTypeObjective77Delivery0.checked, SixTypeObjective77Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective77Delivery1.data, SixTypeObjective77Delivery1.checked, SixTypeObjective77Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective77Delivery2.data, SixTypeObjective77Delivery2.checked, SixTypeObjective77Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective77Delivery3.data, SixTypeObjective77Delivery3.checked, SixTypeObjective77Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective77Delivery4.data, SixTypeObjective77Delivery4.checked, SixTypeObjective77Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective77Delivery5.data, SixTypeObjective77Delivery5.checked, SixTypeObjective77Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate77
