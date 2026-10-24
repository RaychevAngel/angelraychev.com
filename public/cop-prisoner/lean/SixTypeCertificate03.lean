import SixTypeObjective03Transfer
import SixTypeObjective03Delivery0
import SixTypeObjective03Delivery1
import SixTypeObjective03Delivery2
import SixTypeObjective03Delivery3
import SixTypeObjective03Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate03
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern03.pattern := by
  constructor
  · exact ⟨SixTypeObjective03Transfer.data, SixTypeObjective03Transfer.checked, SixTypeObjective03Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective03Delivery0.data, SixTypeObjective03Delivery0.checked, SixTypeObjective03Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective03Delivery1.data, SixTypeObjective03Delivery1.checked, SixTypeObjective03Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective03Delivery2.data, SixTypeObjective03Delivery2.checked, SixTypeObjective03Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective03Delivery3.data, SixTypeObjective03Delivery3.checked, SixTypeObjective03Delivery3.initial_states⟩
    · simp [SixTypePattern03.pattern] at present
    · exact ⟨SixTypeObjective03Delivery5.data, SixTypeObjective03Delivery5.checked, SixTypeObjective03Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate03
