import SixTypeObjective49Transfer
import SixTypeObjective49Delivery0
import SixTypeObjective49Delivery1
import SixTypeObjective49Delivery2
import SixTypeObjective49Delivery3
import SixTypeObjective49Delivery4
import SixTypeObjective49Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate49
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern49.pattern := by
  constructor
  · exact ⟨SixTypeObjective49Transfer.data, SixTypeObjective49Transfer.checked, SixTypeObjective49Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective49Delivery0.data, SixTypeObjective49Delivery0.checked, SixTypeObjective49Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective49Delivery1.data, SixTypeObjective49Delivery1.checked, SixTypeObjective49Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective49Delivery2.data, SixTypeObjective49Delivery2.checked, SixTypeObjective49Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective49Delivery3.data, SixTypeObjective49Delivery3.checked, SixTypeObjective49Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective49Delivery4.data, SixTypeObjective49Delivery4.checked, SixTypeObjective49Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective49Delivery5.data, SixTypeObjective49Delivery5.checked, SixTypeObjective49Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate49
