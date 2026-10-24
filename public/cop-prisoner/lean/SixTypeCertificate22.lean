import SixTypeObjective22Transfer
import SixTypeObjective22Delivery0
import SixTypeObjective22Delivery1
import SixTypeObjective22Delivery2
import SixTypeObjective22Delivery3
import SixTypeObjective22Delivery4
import SixTypeObjective22Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate22
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern22.pattern := by
  constructor
  · exact ⟨SixTypeObjective22Transfer.data, SixTypeObjective22Transfer.checked, SixTypeObjective22Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective22Delivery0.data, SixTypeObjective22Delivery0.checked, SixTypeObjective22Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective22Delivery1.data, SixTypeObjective22Delivery1.checked, SixTypeObjective22Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective22Delivery2.data, SixTypeObjective22Delivery2.checked, SixTypeObjective22Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective22Delivery3.data, SixTypeObjective22Delivery3.checked, SixTypeObjective22Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective22Delivery4.data, SixTypeObjective22Delivery4.checked, SixTypeObjective22Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective22Delivery5.data, SixTypeObjective22Delivery5.checked, SixTypeObjective22Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate22
