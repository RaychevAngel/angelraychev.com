import SixTypeObjective39Transfer
import SixTypeObjective39Delivery0
import SixTypeObjective39Delivery1
import SixTypeObjective39Delivery2
import SixTypeObjective39Delivery3
import SixTypeObjective39Delivery4
import SixTypeObjective39Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate39
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern39.pattern := by
  constructor
  · exact ⟨SixTypeObjective39Transfer.data, SixTypeObjective39Transfer.checked, SixTypeObjective39Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective39Delivery0.data, SixTypeObjective39Delivery0.checked, SixTypeObjective39Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective39Delivery1.data, SixTypeObjective39Delivery1.checked, SixTypeObjective39Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective39Delivery2.data, SixTypeObjective39Delivery2.checked, SixTypeObjective39Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective39Delivery3.data, SixTypeObjective39Delivery3.checked, SixTypeObjective39Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective39Delivery4.data, SixTypeObjective39Delivery4.checked, SixTypeObjective39Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective39Delivery5.data, SixTypeObjective39Delivery5.checked, SixTypeObjective39Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate39
