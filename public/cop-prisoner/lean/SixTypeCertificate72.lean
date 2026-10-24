import SixTypeObjective72Transfer
import SixTypeObjective72Delivery0
import SixTypeObjective72Delivery1
import SixTypeObjective72Delivery2
import SixTypeObjective72Delivery3
import SixTypeObjective72Delivery4
import SixTypeObjective72Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate72
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern72.pattern := by
  constructor
  · exact ⟨SixTypeObjective72Transfer.data, SixTypeObjective72Transfer.checked, SixTypeObjective72Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective72Delivery0.data, SixTypeObjective72Delivery0.checked, SixTypeObjective72Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective72Delivery1.data, SixTypeObjective72Delivery1.checked, SixTypeObjective72Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective72Delivery2.data, SixTypeObjective72Delivery2.checked, SixTypeObjective72Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective72Delivery3.data, SixTypeObjective72Delivery3.checked, SixTypeObjective72Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective72Delivery4.data, SixTypeObjective72Delivery4.checked, SixTypeObjective72Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective72Delivery5.data, SixTypeObjective72Delivery5.checked, SixTypeObjective72Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate72
