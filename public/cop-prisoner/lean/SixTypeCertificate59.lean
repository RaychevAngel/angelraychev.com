import SixTypeObjective59Transfer
import SixTypeObjective59Delivery0
import SixTypeObjective59Delivery1
import SixTypeObjective59Delivery2
import SixTypeObjective59Delivery3
import SixTypeObjective59Delivery4
import SixTypeObjective59Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate59
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern59.pattern := by
  constructor
  · exact ⟨SixTypeObjective59Transfer.data, SixTypeObjective59Transfer.checked, SixTypeObjective59Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective59Delivery0.data, SixTypeObjective59Delivery0.checked, SixTypeObjective59Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective59Delivery1.data, SixTypeObjective59Delivery1.checked, SixTypeObjective59Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective59Delivery2.data, SixTypeObjective59Delivery2.checked, SixTypeObjective59Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective59Delivery3.data, SixTypeObjective59Delivery3.checked, SixTypeObjective59Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective59Delivery4.data, SixTypeObjective59Delivery4.checked, SixTypeObjective59Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective59Delivery5.data, SixTypeObjective59Delivery5.checked, SixTypeObjective59Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate59
