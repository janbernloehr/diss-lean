import NLS.ZakharovShabat.SourceWeightedGapBound
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.SequenceSpaces.SobolevHomogeneous

/-! Complex local bounds for the actual Sobolev weighted squared gaps.
The full ell1 bound also supplies a simultaneous pointwise gap bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolevSquaredGap_bounds (t : ℝ) (ht : 0≤t) (φ : CoeffPair 2) :
    let w := sourceSobolevSpectralWeight t ht
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ G : Set (CoeffPair 2), IsOpen G ∧ φ∈G ∧ ∃ R : ℝ, 0≤R ∧
      ∀ ψ∈G, ∃ h : Coeff 1, ‖h‖≤R ∧
        (∀ k : ℤ, ‖h k‖=Weight.sobolev (2*t) k*
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^2) ∧
        ∀ k : ℤ, Weight.sobolev t k*
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖≤R+1 := by
  intro w L
  obtain ⟨G,hG,hφG,R,hgap⟩ := exists_local_sourceWeightedSquaredGap_bound w L
    (normalizedWeightedPeriodOne w).toContinuousLinearMap
    (weightedBaseToPair_normalizedWeightedPeriodOne w) φ
  obtain ⟨h0,_,h0norm⟩ := hgap φ hφG
  have hR : 0≤R := (norm_nonneg h0).trans h0norm
  refine ⟨G,hG,hφG,R,hR,?_⟩
  intro ψ hψ
  obtain ⟨g,hg,hgnorm⟩ := hgap ψ hψ
  refine ⟨g,hgnorm,?_,?_⟩
  · intro k
    rw [hg k,sourceWeightedSquaredGap,←mul_pow,sourceSobolevSpectralWeight_even,
      norm_pow,Weight.norm_sobolev_mul_sq]
    rfl
  · intro k
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
    have hsq : (Weight.sobolev t k*‖γ k‖)^2=‖g k‖ := by
      rw [hg k,sourceWeightedSquaredGap,norm_mul,norm_pow,norm_pow,
        sourceSobolevSpectralWeight_even,Complex.norm_real,
        Real.norm_of_nonneg ((Weight.sobolev t).positive k).le]
      ring
    have hn := (lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞)≠0) g k).trans hgnorm
    change Weight.sobolev t k*‖γ k‖≤R+1
    nlinarith [sq_nonneg R]

end NLS.ZakharovShabat
