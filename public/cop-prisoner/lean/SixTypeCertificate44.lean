import SixTypeObjective44Transfer
import SixTypeObjective44Delivery0
import SixTypeObjective44Delivery1
import SixTypeObjective44Delivery2
import SixTypeObjective44Delivery3
import SixTypeObjective44Delivery4
import SixTypeObjective44Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate44
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern44.pattern := by
  constructor
  · exact ⟨SixTypeObjective44Transfer.data, SixTypeObjective44Transfer.checked, SixTypeObjective44Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective44Delivery0.data, SixTypeObjective44Delivery0.checked, SixTypeObjective44Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective44Delivery1.data, SixTypeObjective44Delivery1.checked, SixTypeObjective44Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective44Delivery2.data, SixTypeObjective44Delivery2.checked, SixTypeObjective44Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective44Delivery3.data, SixTypeObjective44Delivery3.checked, SixTypeObjective44Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective44Delivery4.data, SixTypeObjective44Delivery4.checked, SixTypeObjective44Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective44Delivery5.data, SixTypeObjective44Delivery5.checked, SixTypeObjective44Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate44
