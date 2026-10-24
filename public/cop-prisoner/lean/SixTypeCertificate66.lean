import SixTypeObjective66Transfer
import SixTypeObjective66Delivery0
import SixTypeObjective66Delivery1
import SixTypeObjective66Delivery2
import SixTypeObjective66Delivery3
import SixTypeObjective66Delivery4
import SixTypeObjective66Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate66
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern66.pattern := by
  constructor
  · exact ⟨SixTypeObjective66Transfer.data, SixTypeObjective66Transfer.checked, SixTypeObjective66Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective66Delivery0.data, SixTypeObjective66Delivery0.checked, SixTypeObjective66Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective66Delivery1.data, SixTypeObjective66Delivery1.checked, SixTypeObjective66Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective66Delivery2.data, SixTypeObjective66Delivery2.checked, SixTypeObjective66Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective66Delivery3.data, SixTypeObjective66Delivery3.checked, SixTypeObjective66Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective66Delivery4.data, SixTypeObjective66Delivery4.checked, SixTypeObjective66Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective66Delivery5.data, SixTypeObjective66Delivery5.checked, SixTypeObjective66Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate66
