import SixTypeObjective76Transfer
import SixTypeObjective76Delivery0
import SixTypeObjective76Delivery1
import SixTypeObjective76Delivery2
import SixTypeObjective76Delivery3
import SixTypeObjective76Delivery4
import SixTypeObjective76Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate76
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern76.pattern := by
  constructor
  · exact ⟨SixTypeObjective76Transfer.data, SixTypeObjective76Transfer.checked, SixTypeObjective76Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective76Delivery0.data, SixTypeObjective76Delivery0.checked, SixTypeObjective76Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective76Delivery1.data, SixTypeObjective76Delivery1.checked, SixTypeObjective76Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective76Delivery2.data, SixTypeObjective76Delivery2.checked, SixTypeObjective76Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective76Delivery3.data, SixTypeObjective76Delivery3.checked, SixTypeObjective76Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective76Delivery4.data, SixTypeObjective76Delivery4.checked, SixTypeObjective76Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective76Delivery5.data, SixTypeObjective76Delivery5.checked, SixTypeObjective76Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate76
