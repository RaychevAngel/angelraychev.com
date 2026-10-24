import SixTypeObjective69Transfer
import SixTypeObjective69Delivery0
import SixTypeObjective69Delivery1
import SixTypeObjective69Delivery2
import SixTypeObjective69Delivery3
import SixTypeObjective69Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate69
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern69.pattern := by
  constructor
  · exact ⟨SixTypeObjective69Transfer.data, SixTypeObjective69Transfer.checked, SixTypeObjective69Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective69Delivery0.data, SixTypeObjective69Delivery0.checked, SixTypeObjective69Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective69Delivery1.data, SixTypeObjective69Delivery1.checked, SixTypeObjective69Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective69Delivery2.data, SixTypeObjective69Delivery2.checked, SixTypeObjective69Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective69Delivery3.data, SixTypeObjective69Delivery3.checked, SixTypeObjective69Delivery3.initial_states⟩
    · simp [SixTypePattern69.pattern] at present
    · exact ⟨SixTypeObjective69Delivery5.data, SixTypeObjective69Delivery5.checked, SixTypeObjective69Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate69
