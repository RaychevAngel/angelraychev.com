import SixTypeObjective09Transfer
import SixTypeObjective09Delivery0
import SixTypeObjective09Delivery1
import SixTypeObjective09Delivery2
import SixTypeObjective09Delivery3
import SixTypeObjective09Delivery4
import SixTypeObjective09Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate09
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern09.pattern := by
  constructor
  · exact ⟨SixTypeObjective09Transfer.data, SixTypeObjective09Transfer.checked, SixTypeObjective09Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective09Delivery0.data, SixTypeObjective09Delivery0.checked, SixTypeObjective09Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective09Delivery1.data, SixTypeObjective09Delivery1.checked, SixTypeObjective09Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective09Delivery2.data, SixTypeObjective09Delivery2.checked, SixTypeObjective09Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective09Delivery3.data, SixTypeObjective09Delivery3.checked, SixTypeObjective09Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective09Delivery4.data, SixTypeObjective09Delivery4.checked, SixTypeObjective09Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective09Delivery5.data, SixTypeObjective09Delivery5.checked, SixTypeObjective09Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate09
