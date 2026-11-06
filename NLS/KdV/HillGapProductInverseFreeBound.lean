import NLS.KdV.HillDirichletNumeratorExteriorDecay
import NLS.KdV.HillEnergyCircleFrequencySeparation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- The actual full gap product uniformly bounds the reciprocal free
Dirichlet factor on sufficiently large central energy circles. -/
theorem exists_hillGapFullEnergyProduct_inverse_free_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
      hillAbelianNumeratorProduct roots 0 E ≠ 0 ∧
      ‖(sin (Complex.sqrt E)/Complex.sqrt E)/hillAbelianNumeratorProduct roots 0 E‖ ≤ 2 := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillGapSignedRootFrequency roots)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr roots hroots)
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨K,?_⟩
  intro k hk E hE
  have hz := hillEnergyCircle_sqrt_mem_centralCircle k E hE
  have hsin : sin (Complex.sqrt E) ≠ 0 := sin_ne_zero_on_centralCircle k _ hz
  have hz0 : Complex.sqrt E ≠ 0 := by
    intro hh
    have ht : ‖Complex.sqrt E‖ = centralCircleRadius k := by
      simpa only [mem_sphere,dist_zero_right] using hz
    rw [hh,norm_zero] at ht
    linarith [centralCircleRadius_pos k]
  have hb := hK k hk (Complex.sqrt E) hz
  rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q hq hr roots hroots,
    complex_sqrt_sq] at hb
  have he : (-2*Complex.sqrt E*hillAbelianNumeratorProduct roots 0 E)/(-2*sin (Complex.sqrt E)) =
      hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E) := by
    field_simp
  rw [he] at hb
  have hh := norm_le_norm_sub_add (1 : ℂ)
    (hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E))
  rw [norm_one,norm_sub_rev] at hh
  have hlo : (1:ℝ)/2 ≤ ‖hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E)‖ := by
    linarith
  have hp : hillAbelianNumeratorProduct roots 0 E ≠ 0 := by
    intro ht
    rw [ht,zero_div,norm_zero] at hlo
    norm_num at hlo
  refine ⟨hp,?_⟩
  have hi : (sin (Complex.sqrt E)/Complex.sqrt E)/hillAbelianNumeratorProduct roots 0 E =
      (hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E))⁻¹ := by
    field_simp
  rw [hi,norm_inv]
  rw [← one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E)‖)).mpr
  linarith

end NLS.KdV
