import SixTypeObjective61Transfer
import SixTypeObjective61Delivery0
import SixTypeObjective61Delivery1
import SixTypeObjective61Delivery2
import SixTypeObjective61Delivery3
import SixTypeObjective61Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate61
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern61.pattern := by
  constructor
  · exact ⟨SixTypeObjective61Transfer.data, SixTypeObjective61Transfer.checked, SixTypeObjective61Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective61Delivery0.data, SixTypeObjective61Delivery0.checked, SixTypeObjective61Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective61Delivery1.data, SixTypeObjective61Delivery1.checked, SixTypeObjective61Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective61Delivery2.data, SixTypeObjective61Delivery2.checked, SixTypeObjective61Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective61Delivery3.data, SixTypeObjective61Delivery3.checked, SixTypeObjective61Delivery3.initial_states⟩
    · simp [SixTypePattern61.pattern] at present
    · exact ⟨SixTypeObjective61Delivery5.data, SixTypeObjective61Delivery5.checked, SixTypeObjective61Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate61
