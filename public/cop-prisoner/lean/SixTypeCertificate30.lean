import SixTypeObjective30Transfer
import SixTypeObjective30Delivery0
import SixTypeObjective30Delivery1
import SixTypeObjective30Delivery2
import SixTypeObjective30Delivery3
import SixTypeObjective30Delivery4
import SixTypeObjective30Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate30
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern30.pattern := by
  constructor
  · exact ⟨SixTypeObjective30Transfer.data, SixTypeObjective30Transfer.checked, SixTypeObjective30Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective30Delivery0.data, SixTypeObjective30Delivery0.checked, SixTypeObjective30Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective30Delivery1.data, SixTypeObjective30Delivery1.checked, SixTypeObjective30Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective30Delivery2.data, SixTypeObjective30Delivery2.checked, SixTypeObjective30Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective30Delivery3.data, SixTypeObjective30Delivery3.checked, SixTypeObjective30Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective30Delivery4.data, SixTypeObjective30Delivery4.checked, SixTypeObjective30Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective30Delivery5.data, SixTypeObjective30Delivery5.checked, SixTypeObjective30Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate30
