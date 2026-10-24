import OddEndpointObjective050Transfer
import OddEndpointObjective050Delivery0
import OddEndpointObjective050Delivery1
import OddEndpointObjective050Delivery2
import OddEndpointObjective050Delivery3
import OddEndpointObjective050Delivery4
import OddEndpointObjective050Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate050
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern050
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective050Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective050Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective050Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective050Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective050Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective050Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective050Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate050
