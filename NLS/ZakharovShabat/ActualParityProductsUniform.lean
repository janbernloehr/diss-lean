import NLS.ZakharovShabat.CompleteParityDisplacementBounds
import NLS.ZakharovShabat.ParitySpectralFamilies

/-!
# Actual parity products uniform in potential and spectral parameter

One open convex potential neighborhood supplies completed actual parity roots
with a common displacement bound. Both literal parity cutoffs then converge
uniformly over all even-supported potentials in that neighborhood and every
compact spectral set, including spectral collisions and the free lattice.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual even-supported potentials admit whole-plane parity convergence uniform over one common neighborhood. -/
theorem exists_uniform_actualParityProducts_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      let V := {ψ : WeightedCoeffPair w.toWeight p // ψ ∈ U ∧ weightedBaseToPair w ψ ∈ pairParitySubspace 0}
      ∃ ξ η : V → ℤ → ℂ, ∃ h : ∀ ψ : V, CompletePeriodicParityPairs hp w ψ.val N₀ (ξ ψ) (η ψ),
        (∃ R : ℝ, 0 ≤ R ∧ ∀ ψ : V,
          ‖(⟨_,(h ψ).left_displacement⟩ : Coeff p)‖ ≤ R ∧
          ‖(⟨_,(h ψ).right_displacement⟩ : Coeff p)‖ ≤ R) ∧
        ∀ K : Set ℂ, IsCompact K →
          TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) => evenSpectralPairCutoff (ξ t.2) (η t.2) t.1 M)
            (fun t => evenSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) ∧
          TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) => oddSpectralPairCutoff (ξ t.2) (η t.2) t.1 M)
            (fun t => oddSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) := by
  obtain ⟨N,hN,U,ho,hconv,hφ,h0,R,hR,hdata⟩ := exists_uniform_bounded_completePeriodicParityPairs hp hp1 w φ
  let V := {ψ : WeightedCoeffPair w.toWeight p // ψ ∈ U ∧ weightedBaseToPair w ψ ∈ pairParitySubspace 0}
  choose ξ η h hbξ hbη using (fun ψ : V => hdata ψ.val ψ.property.1 ψ.property.2)
  refine ⟨N,hN,U,ho,hconv,hφ,h0,ξ,η,h,⟨R,hR,fun ψ => ⟨hbξ ψ,hbη ψ⟩⟩,?_⟩
  intro K hK
  exact tendstoUniformlyOn_paritySpectralProducts_family hp hp1 ξ η
    (fun ψ => (h ψ).left_displacement) (fun ψ => (h ψ).right_displacement) R hR hbξ hbη K hK

end NLS.ZakharovShabat
