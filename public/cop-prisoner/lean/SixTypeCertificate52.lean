import SixTypeObjective52Transfer
import SixTypeObjective52Delivery0
import SixTypeObjective52Delivery1
import SixTypeObjective52Delivery2
import SixTypeObjective52Delivery3
import SixTypeObjective52Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate52
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern52.pattern := by
  constructor
  · exact ⟨SixTypeObjective52Transfer.data, SixTypeObjective52Transfer.checked, SixTypeObjective52Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective52Delivery0.data, SixTypeObjective52Delivery0.checked, SixTypeObjective52Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective52Delivery1.data, SixTypeObjective52Delivery1.checked, SixTypeObjective52Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective52Delivery2.data, SixTypeObjective52Delivery2.checked, SixTypeObjective52Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective52Delivery3.data, SixTypeObjective52Delivery3.checked, SixTypeObjective52Delivery3.initial_states⟩
    · simp [SixTypePattern52.pattern] at present
    · exact ⟨SixTypeObjective52Delivery5.data, SixTypeObjective52Delivery5.checked, SixTypeObjective52Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate52
