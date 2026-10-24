import SixTypeObjective31Transfer
import SixTypeObjective31Delivery0
import SixTypeObjective31Delivery1
import SixTypeObjective31Delivery2
import SixTypeObjective31Delivery3
import SixTypeObjective31Delivery4
import SixTypeObjective31Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate31
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern31.pattern := by
  constructor
  · exact ⟨SixTypeObjective31Transfer.data, SixTypeObjective31Transfer.checked, SixTypeObjective31Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective31Delivery0.data, SixTypeObjective31Delivery0.checked, SixTypeObjective31Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective31Delivery1.data, SixTypeObjective31Delivery1.checked, SixTypeObjective31Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective31Delivery2.data, SixTypeObjective31Delivery2.checked, SixTypeObjective31Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective31Delivery3.data, SixTypeObjective31Delivery3.checked, SixTypeObjective31Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective31Delivery4.data, SixTypeObjective31Delivery4.checked, SixTypeObjective31Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective31Delivery5.data, SixTypeObjective31Delivery5.checked, SixTypeObjective31Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate31
