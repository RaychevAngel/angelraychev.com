import SixTypeObjective55Transfer
import SixTypeObjective55Delivery0
import SixTypeObjective55Delivery1
import SixTypeObjective55Delivery2
import SixTypeObjective55Delivery3
import SixTypeObjective55Delivery4
import SixTypeObjective55Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate55
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern55.pattern := by
  constructor
  · exact ⟨SixTypeObjective55Transfer.data, SixTypeObjective55Transfer.checked, SixTypeObjective55Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective55Delivery0.data, SixTypeObjective55Delivery0.checked, SixTypeObjective55Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective55Delivery1.data, SixTypeObjective55Delivery1.checked, SixTypeObjective55Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective55Delivery2.data, SixTypeObjective55Delivery2.checked, SixTypeObjective55Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective55Delivery3.data, SixTypeObjective55Delivery3.checked, SixTypeObjective55Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective55Delivery4.data, SixTypeObjective55Delivery4.checked, SixTypeObjective55Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective55Delivery5.data, SixTypeObjective55Delivery5.checked, SixTypeObjective55Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate55
