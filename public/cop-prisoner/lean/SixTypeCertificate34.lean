import SixTypeObjective34Transfer
import SixTypeObjective34Delivery0
import SixTypeObjective34Delivery1
import SixTypeObjective34Delivery2
import SixTypeObjective34Delivery3
import SixTypeObjective34Delivery4
import SixTypeObjective34Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate34
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern34.pattern := by
  constructor
  · exact ⟨SixTypeObjective34Transfer.data, SixTypeObjective34Transfer.checked, SixTypeObjective34Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective34Delivery0.data, SixTypeObjective34Delivery0.checked, SixTypeObjective34Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective34Delivery1.data, SixTypeObjective34Delivery1.checked, SixTypeObjective34Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective34Delivery2.data, SixTypeObjective34Delivery2.checked, SixTypeObjective34Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective34Delivery3.data, SixTypeObjective34Delivery3.checked, SixTypeObjective34Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective34Delivery4.data, SixTypeObjective34Delivery4.checked, SixTypeObjective34Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective34Delivery5.data, SixTypeObjective34Delivery5.checked, SixTypeObjective34Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate34
