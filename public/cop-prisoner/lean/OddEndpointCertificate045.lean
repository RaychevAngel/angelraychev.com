import OddEndpointObjective045Transfer
import OddEndpointObjective045Delivery0
import OddEndpointObjective045Delivery1
import OddEndpointObjective045Delivery2
import OddEndpointObjective045Delivery3
import OddEndpointObjective045Delivery4
import OddEndpointObjective045Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate045
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern045
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective045Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective045Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective045Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective045Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective045Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective045Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective045Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate045
