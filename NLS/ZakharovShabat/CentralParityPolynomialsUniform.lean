import NLS.ZakharovShabat.ParityBoundaryUniform
import NLS.ZakharovShabat.ActualParityProductsUniform
import NLS.ZakharovShabat.CentralParityPolynomialAnalytic

/-!
# Joint uniform convergence of intrinsic parity approximants

The even approximants are the literal even cutoffs. Uniform nonvanishing of
the odd boundary pair permits its removal. Both intrinsic polynomial sequences
therefore converge uniformly on spectral compact sets over actual potential
neighborhoods, with a common sequence index `2M`.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Intrinsic doubled central parity polynomials converge uniformly over every bounded actual family. -/
theorem tendstoUniformlyOn_normalizedCentralParity_family {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : X → WeightedCoeffPair w.toWeight p)
    (N : ℕ) (ξ η : X → ℤ → ℂ) (h : ∀ x, CompletePeriodicParityPairs hp w (φ x) N (ξ x) (η x))
    (R : ℝ) (hR : 0 ≤ R)
    (hbξ : ∀ x, ‖(⟨_,(h x).left_displacement⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,(h x).right_displacement⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) =>
      normalizedCentralParityPolynomial hp (weightedBaseToPair w (φ t.2)) (2*M) 0 t.1)
      (fun t => evenSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) ∧
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) =>
      normalizedCentralParityPolynomial hp (weightedBaseToPair w (φ t.2)) (2*M) 1 t.1)
      (fun t => oddSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) := by
  have hξ x := (h x).left_displacement
  have hη x := (h x).right_displacement
  have hraw := tendstoUniformlyOn_paritySpectralProducts_family hp hp1 ξ η hξ hη R hR hbξ hbη K hK
  constructor
  · apply hraw.1.congr
    filter_upwards [eventually_ge_atTop N] with M hM t _
    exact ((h t.2).cutoffs_eq_normalizedParity M (by omega) t.1).1
  · let B (M : ℕ) (t : ℂ × X) := spectralPairFactor (ξ t.2) (η t.2) t.1 (2*(M : ℤ)+1)
    have hboundary := tendstoUniformlyOn_oddBoundary_family ξ η hξ hη R hbξ hbη K hK
    obtain ⟨hinv,hne⟩ := NLS.ComplexAnalysis.uniform_inverse_of_tendsto_one B (K ×ˢ Set.univ) hboundary
    have hsξ x : ‖(⟨_,memℓp_parityRescale hp (ξ x) (hξ x) 1⟩ : Coeff p)‖ ≤ R :=
      (norm_parityRescale_displacement_le hp (ξ x) (hξ x) 1).trans (hbξ x)
    have hsη x : ‖(⟨_,memℓp_parityRescale hp (η x) (hη x) 1⟩ : Coeff p)‖ ≤ R :=
      (norm_parityRescale_displacement_le hp (η x) (hη x) 1).trans (hbη x)
    obtain ⟨A,hA,hAb⟩ := exists_bound_entireSpectralPairProduct_family hp hp1
      (fun x => parityRescale (ξ x) 1) (fun x => parityRescale (η x) 1)
      (fun x => memℓp_parityRescale hp (ξ x) (hξ x) 1) (fun x => memℓp_parityRescale hp (η x) (hη x) 1)
      R hR hsξ hsη ((fun z : ℂ => (z-(Real.pi : ℂ))/2) '' K) (hK.image (by fun_prop))
    have hodd : ∀ t ∈ K ×ˢ (Set.univ : Set X), ‖oddSpectralPairProduct (ξ t.2) (η t.2) t.1‖ ≤ A := by
      intro t ht
      simpa only [oddSpectralPairProduct, norm_neg] using
        hAb ((t.1-(Real.pi : ℂ))/2,t.2) ⟨⟨t.1,ht.1,rfl⟩,Set.mem_univ _⟩
    have hh := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ (K ×ˢ Set.univ) A 1 hA
      (by norm_num) hraw.2 hinv hodd (fun _ _ => by norm_num)
    simp only [mul_one] at hh
    apply hh.congr
    filter_upwards [eventually_ge_atTop N,hne] with M hM hn t ht
    change oddSpectralPairCutoff (ξ t.2) (η t.2) t.1 M * (B M t)⁻¹ = _
    rw [((h t.2).cutoffs_eq_normalizedParity M (by omega) t.1).2]
    change (_ * B M t) * (B M t)⁻¹ = _
    rw [mul_assoc, mul_inv_cancel₀ (hn t ht), mul_one]

/-- One actual potential neighborhood supports joint uniform convergence of both analytic intrinsic parity approximants. -/
theorem exists_uniform_normalizedCentralParityProducts_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      let V := {ψ : WeightedCoeffPair w.toWeight p // ψ ∈ U ∧ weightedBaseToPair w ψ ∈ pairParitySubspace 0}
      ∃ ξ η : V → ℤ → ℂ, ∃ _h : ∀ ψ : V, CompletePeriodicParityPairs hp w ψ.val N₀ (ξ ψ) (η ψ),
        ∀ K : Set ℂ, IsCompact K →
          TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) =>
            normalizedCentralParityPolynomial hp (weightedBaseToPair w t.2.val) (2*M) 0 t.1)
            (fun t => evenSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) ∧
          TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) =>
            normalizedCentralParityPolynomial hp (weightedBaseToPair w t.2.val) (2*M) 1 t.1)
            (fun t => oddSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) := by
  obtain ⟨N,hN,U,ho,hconv,hφ,h0,ξ,η,h,⟨R,hR,hb⟩,_⟩ := exists_uniform_actualParityProducts_joint hp hp1 w φ
  refine ⟨N,hN,U,ho,hconv,hφ,h0,ξ,η,h,?_⟩
  intro K hK
  exact tendstoUniformlyOn_normalizedCentralParity_family hp hp1 w Subtype.val N ξ η h R hR
    (fun x => (hb x).1) (fun x => (hb x).2) K hK

end NLS.ZakharovShabat
