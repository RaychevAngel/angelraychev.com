import SixTypeObjective40Transfer
import SixTypeObjective40Delivery0
import SixTypeObjective40Delivery1
import SixTypeObjective40Delivery2
import SixTypeObjective40Delivery3
import SixTypeObjective40Delivery4
import SixTypeObjective40Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate40
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern40.pattern := by
  constructor
  · exact ⟨SixTypeObjective40Transfer.data, SixTypeObjective40Transfer.checked, SixTypeObjective40Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective40Delivery0.data, SixTypeObjective40Delivery0.checked, SixTypeObjective40Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective40Delivery1.data, SixTypeObjective40Delivery1.checked, SixTypeObjective40Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective40Delivery2.data, SixTypeObjective40Delivery2.checked, SixTypeObjective40Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective40Delivery3.data, SixTypeObjective40Delivery3.checked, SixTypeObjective40Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective40Delivery4.data, SixTypeObjective40Delivery4.checked, SixTypeObjective40Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective40Delivery5.data, SixTypeObjective40Delivery5.checked, SixTypeObjective40Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate40
