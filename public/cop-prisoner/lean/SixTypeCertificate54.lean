import SixTypeObjective54Transfer
import SixTypeObjective54Delivery0
import SixTypeObjective54Delivery1
import SixTypeObjective54Delivery2
import SixTypeObjective54Delivery3
import SixTypeObjective54Delivery4
import SixTypeObjective54Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate54
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern54.pattern := by
  constructor
  · exact ⟨SixTypeObjective54Transfer.data, SixTypeObjective54Transfer.checked, SixTypeObjective54Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective54Delivery0.data, SixTypeObjective54Delivery0.checked, SixTypeObjective54Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective54Delivery1.data, SixTypeObjective54Delivery1.checked, SixTypeObjective54Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective54Delivery2.data, SixTypeObjective54Delivery2.checked, SixTypeObjective54Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective54Delivery3.data, SixTypeObjective54Delivery3.checked, SixTypeObjective54Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective54Delivery4.data, SixTypeObjective54Delivery4.checked, SixTypeObjective54Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective54Delivery5.data, SixTypeObjective54Delivery5.checked, SixTypeObjective54Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate54
