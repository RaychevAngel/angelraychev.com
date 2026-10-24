import SixTypeObjective60Transfer
import SixTypeObjective60Delivery0
import SixTypeObjective60Delivery1
import SixTypeObjective60Delivery2
import SixTypeObjective60Delivery3
import SixTypeObjective60Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate60
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern60.pattern := by
  constructor
  · exact ⟨SixTypeObjective60Transfer.data, SixTypeObjective60Transfer.checked, SixTypeObjective60Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective60Delivery0.data, SixTypeObjective60Delivery0.checked, SixTypeObjective60Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective60Delivery1.data, SixTypeObjective60Delivery1.checked, SixTypeObjective60Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective60Delivery2.data, SixTypeObjective60Delivery2.checked, SixTypeObjective60Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective60Delivery3.data, SixTypeObjective60Delivery3.checked, SixTypeObjective60Delivery3.initial_states⟩
    · simp [SixTypePattern60.pattern] at present
    · exact ⟨SixTypeObjective60Delivery5.data, SixTypeObjective60Delivery5.checked, SixTypeObjective60Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate60
