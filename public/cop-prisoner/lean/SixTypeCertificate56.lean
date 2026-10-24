import SixTypeObjective56Transfer
import SixTypeObjective56Delivery0
import SixTypeObjective56Delivery1
import SixTypeObjective56Delivery2
import SixTypeObjective56Delivery3
import SixTypeObjective56Delivery4
import SixTypeObjective56Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate56
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern56.pattern := by
  constructor
  · exact ⟨SixTypeObjective56Transfer.data, SixTypeObjective56Transfer.checked, SixTypeObjective56Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective56Delivery0.data, SixTypeObjective56Delivery0.checked, SixTypeObjective56Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective56Delivery1.data, SixTypeObjective56Delivery1.checked, SixTypeObjective56Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective56Delivery2.data, SixTypeObjective56Delivery2.checked, SixTypeObjective56Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective56Delivery3.data, SixTypeObjective56Delivery3.checked, SixTypeObjective56Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective56Delivery4.data, SixTypeObjective56Delivery4.checked, SixTypeObjective56Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective56Delivery5.data, SixTypeObjective56Delivery5.checked, SixTypeObjective56Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate56
