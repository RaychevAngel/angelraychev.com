import SixTypeObjective16Transfer
import SixTypeObjective16Delivery0
import SixTypeObjective16Delivery1
import SixTypeObjective16Delivery2
import SixTypeObjective16Delivery3
import SixTypeObjective16Delivery4
import SixTypeObjective16Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate16
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern16.pattern := by
  constructor
  · exact ⟨SixTypeObjective16Transfer.data, SixTypeObjective16Transfer.checked, SixTypeObjective16Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective16Delivery0.data, SixTypeObjective16Delivery0.checked, SixTypeObjective16Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective16Delivery1.data, SixTypeObjective16Delivery1.checked, SixTypeObjective16Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective16Delivery2.data, SixTypeObjective16Delivery2.checked, SixTypeObjective16Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective16Delivery3.data, SixTypeObjective16Delivery3.checked, SixTypeObjective16Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective16Delivery4.data, SixTypeObjective16Delivery4.checked, SixTypeObjective16Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective16Delivery5.data, SixTypeObjective16Delivery5.checked, SixTypeObjective16Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate16
