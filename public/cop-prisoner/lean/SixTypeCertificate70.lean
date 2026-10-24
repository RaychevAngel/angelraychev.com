import SixTypeObjective70Transfer
import SixTypeObjective70Delivery0
import SixTypeObjective70Delivery1
import SixTypeObjective70Delivery2
import SixTypeObjective70Delivery3
import SixTypeObjective70Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate70
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern70.pattern := by
  constructor
  · exact ⟨SixTypeObjective70Transfer.data, SixTypeObjective70Transfer.checked, SixTypeObjective70Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective70Delivery0.data, SixTypeObjective70Delivery0.checked, SixTypeObjective70Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective70Delivery1.data, SixTypeObjective70Delivery1.checked, SixTypeObjective70Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective70Delivery2.data, SixTypeObjective70Delivery2.checked, SixTypeObjective70Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective70Delivery3.data, SixTypeObjective70Delivery3.checked, SixTypeObjective70Delivery3.initial_states⟩
    · simp [SixTypePattern70.pattern] at present
    · exact ⟨SixTypeObjective70Delivery5.data, SixTypeObjective70Delivery5.checked, SixTypeObjective70Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate70
