import SixTypeObjective32Transfer
import SixTypeObjective32Delivery0
import SixTypeObjective32Delivery1
import SixTypeObjective32Delivery2
import SixTypeObjective32Delivery3
import SixTypeObjective32Delivery4
import SixTypeObjective32Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate32
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern32.pattern := by
  constructor
  · exact ⟨SixTypeObjective32Transfer.data, SixTypeObjective32Transfer.checked, SixTypeObjective32Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective32Delivery0.data, SixTypeObjective32Delivery0.checked, SixTypeObjective32Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective32Delivery1.data, SixTypeObjective32Delivery1.checked, SixTypeObjective32Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective32Delivery2.data, SixTypeObjective32Delivery2.checked, SixTypeObjective32Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective32Delivery3.data, SixTypeObjective32Delivery3.checked, SixTypeObjective32Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective32Delivery4.data, SixTypeObjective32Delivery4.checked, SixTypeObjective32Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective32Delivery5.data, SixTypeObjective32Delivery5.checked, SixTypeObjective32Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate32
