import SixTypeObjective12Transfer
import SixTypeObjective12Delivery0
import SixTypeObjective12Delivery1
import SixTypeObjective12Delivery2
import SixTypeObjective12Delivery3
import SixTypeObjective12Delivery4
import SixTypeObjective12Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate12
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern12.pattern := by
  constructor
  · exact ⟨SixTypeObjective12Transfer.data, SixTypeObjective12Transfer.checked, SixTypeObjective12Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective12Delivery0.data, SixTypeObjective12Delivery0.checked, SixTypeObjective12Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective12Delivery1.data, SixTypeObjective12Delivery1.checked, SixTypeObjective12Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective12Delivery2.data, SixTypeObjective12Delivery2.checked, SixTypeObjective12Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective12Delivery3.data, SixTypeObjective12Delivery3.checked, SixTypeObjective12Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective12Delivery4.data, SixTypeObjective12Delivery4.checked, SixTypeObjective12Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective12Delivery5.data, SixTypeObjective12Delivery5.checked, SixTypeObjective12Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate12
