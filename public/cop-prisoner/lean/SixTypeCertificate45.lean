import SixTypeObjective45Transfer
import SixTypeObjective45Delivery0
import SixTypeObjective45Delivery1
import SixTypeObjective45Delivery2
import SixTypeObjective45Delivery3
import SixTypeObjective45Delivery4
import SixTypeObjective45Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate45
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern45.pattern := by
  constructor
  · exact ⟨SixTypeObjective45Transfer.data, SixTypeObjective45Transfer.checked, SixTypeObjective45Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective45Delivery0.data, SixTypeObjective45Delivery0.checked, SixTypeObjective45Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective45Delivery1.data, SixTypeObjective45Delivery1.checked, SixTypeObjective45Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective45Delivery2.data, SixTypeObjective45Delivery2.checked, SixTypeObjective45Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective45Delivery3.data, SixTypeObjective45Delivery3.checked, SixTypeObjective45Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective45Delivery4.data, SixTypeObjective45Delivery4.checked, SixTypeObjective45Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective45Delivery5.data, SixTypeObjective45Delivery5.checked, SixTypeObjective45Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate45
