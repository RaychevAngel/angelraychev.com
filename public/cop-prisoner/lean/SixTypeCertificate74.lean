import SixTypeObjective74Transfer
import SixTypeObjective74Delivery0
import SixTypeObjective74Delivery1
import SixTypeObjective74Delivery2
import SixTypeObjective74Delivery3
import SixTypeObjective74Delivery4
import SixTypeObjective74Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate74
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern74.pattern := by
  constructor
  · exact ⟨SixTypeObjective74Transfer.data, SixTypeObjective74Transfer.checked, SixTypeObjective74Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective74Delivery0.data, SixTypeObjective74Delivery0.checked, SixTypeObjective74Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective74Delivery1.data, SixTypeObjective74Delivery1.checked, SixTypeObjective74Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective74Delivery2.data, SixTypeObjective74Delivery2.checked, SixTypeObjective74Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective74Delivery3.data, SixTypeObjective74Delivery3.checked, SixTypeObjective74Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective74Delivery4.data, SixTypeObjective74Delivery4.checked, SixTypeObjective74Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective74Delivery5.data, SixTypeObjective74Delivery5.checked, SixTypeObjective74Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate74
