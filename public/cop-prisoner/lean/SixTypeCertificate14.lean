import SixTypeObjective14Transfer
import SixTypeObjective14Delivery0
import SixTypeObjective14Delivery1
import SixTypeObjective14Delivery2
import SixTypeObjective14Delivery3
import SixTypeObjective14Delivery4
import SixTypeObjective14Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate14
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern14.pattern := by
  constructor
  · exact ⟨SixTypeObjective14Transfer.data, SixTypeObjective14Transfer.checked, SixTypeObjective14Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective14Delivery0.data, SixTypeObjective14Delivery0.checked, SixTypeObjective14Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective14Delivery1.data, SixTypeObjective14Delivery1.checked, SixTypeObjective14Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective14Delivery2.data, SixTypeObjective14Delivery2.checked, SixTypeObjective14Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective14Delivery3.data, SixTypeObjective14Delivery3.checked, SixTypeObjective14Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective14Delivery4.data, SixTypeObjective14Delivery4.checked, SixTypeObjective14Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective14Delivery5.data, SixTypeObjective14Delivery5.checked, SixTypeObjective14Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate14
