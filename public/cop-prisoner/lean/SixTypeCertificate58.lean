import SixTypeObjective58Transfer
import SixTypeObjective58Delivery0
import SixTypeObjective58Delivery1
import SixTypeObjective58Delivery2
import SixTypeObjective58Delivery3
import SixTypeObjective58Delivery4
import SixTypeObjective58Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate58
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern58.pattern := by
  constructor
  · exact ⟨SixTypeObjective58Transfer.data, SixTypeObjective58Transfer.checked, SixTypeObjective58Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective58Delivery0.data, SixTypeObjective58Delivery0.checked, SixTypeObjective58Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective58Delivery1.data, SixTypeObjective58Delivery1.checked, SixTypeObjective58Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective58Delivery2.data, SixTypeObjective58Delivery2.checked, SixTypeObjective58Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective58Delivery3.data, SixTypeObjective58Delivery3.checked, SixTypeObjective58Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective58Delivery4.data, SixTypeObjective58Delivery4.checked, SixTypeObjective58Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective58Delivery5.data, SixTypeObjective58Delivery5.checked, SixTypeObjective58Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate58
