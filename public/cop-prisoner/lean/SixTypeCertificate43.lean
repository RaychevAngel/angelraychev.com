import SixTypeObjective43Transfer
import SixTypeObjective43Delivery0
import SixTypeObjective43Delivery1
import SixTypeObjective43Delivery2
import SixTypeObjective43Delivery3
import SixTypeObjective43Delivery4
import SixTypeObjective43Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate43
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern43.pattern := by
  constructor
  · exact ⟨SixTypeObjective43Transfer.data, SixTypeObjective43Transfer.checked, SixTypeObjective43Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective43Delivery0.data, SixTypeObjective43Delivery0.checked, SixTypeObjective43Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective43Delivery1.data, SixTypeObjective43Delivery1.checked, SixTypeObjective43Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective43Delivery2.data, SixTypeObjective43Delivery2.checked, SixTypeObjective43Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective43Delivery3.data, SixTypeObjective43Delivery3.checked, SixTypeObjective43Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective43Delivery4.data, SixTypeObjective43Delivery4.checked, SixTypeObjective43Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective43Delivery5.data, SixTypeObjective43Delivery5.checked, SixTypeObjective43Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate43
