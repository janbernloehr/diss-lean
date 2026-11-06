import NLS.KdV.HillFreeDirichletCentralCount
import NLS.ComplexAnalysis.Rouche

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- One cutoff controls the exact original Dirichlet zero count on
every expanding central energy circle for all complex sources in a ball. -/
theorem exists_hillDirichletCharacteristic_central_zero_counts (B : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ p : Coeff 2, ‖p‖≤B →
      (∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2), hillL2DirichletCharacteristic p E≠0) ∧
      analyticZeroCount (hillL2DirichletCharacteristic p)
        (closedBall (0 : ℂ) ((centralCircleRadius k)^2))=k := by
  obtain ⟨K,hK⟩ := exists_hillDirichletCharacteristic_central_relative_bounds B
  refine ⟨K,?_⟩
  intro k hk p hp
  have hbound (E : ℂ) (hE : E∈sphere (0 : ℂ) ((centralCircleRadius k)^2)) :
      hillL2DirichletCharacteristic p E≠0 ∧
        ‖hillL2DirichletCharacteristic p E/hillL2DirichletCharacteristic 0 E-1‖≤1/2 := by
    have hnorm : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
    have hz : Complex.sqrt E∈sphere (0 : ℂ) (centralCircleRadius k) := by
      have hh := congrArg norm (complex_sqrt_sq E)
      rw [norm_pow,hnorm] at hh
      rw [mem_sphere,dist_zero_right]
      nlinarith [norm_nonneg (Complex.sqrt E),centralCircleRadius_pos k]
    have hz0 : Complex.sqrt E≠0 := by
      intro hh
      rw [hh,mem_sphere,dist_zero_right,norm_zero] at hz
      linarith [centralCircleRadius_pos k]
    have hh := hK k hk p hp (Complex.sqrt E) hz
    rw [← hillL2DirichletCharacteristic_free_sq (Complex.sqrt E) hz0,complex_sqrt_sq] at hh
    exact ⟨hh.1,hh.2.1⟩
  have hlt (E : ℂ) (hE : E∈sphere (0 : ℂ) ((centralCircleRadius k)^2)) :
      ‖hillL2DirichletCharacteristic p E-hillL2DirichletCharacteristic 0 E‖<
        ‖hillL2DirichletCharacteristic 0 E‖ := by
    have hh := (hbound E hE).2
    have hfree : hillL2DirichletCharacteristic 0 E≠0 := by
      intro he
      rw [he,div_zero,zero_sub,norm_neg,norm_one] at hh
      norm_num at hh
    rw [show hillL2DirichletCharacteristic p E/hillL2DirichletCharacteristic 0 E-1=
      (hillL2DirichletCharacteristic p E-hillL2DirichletCharacteristic 0 E)/
        hillL2DirichletCharacteristic 0 E by field_simp,norm_div] at hh
    have hpos := norm_pos_iff.mpr hfree
    have ht := (div_le_iff₀ hpos).mp hh
    linarith
  refine ⟨fun E hE => (hbound E hE).1,?_⟩
  exact (analyticZeroCount_eq_of_boundary_lt (sq_pos_of_pos (centralCircleRadius_pos k))
    ((analyticOnNhd_hillL2DirichletCharacteristic 0).mono (subset_univ _))
    ((analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _)) hlt).trans
      (hillL2DirichletCharacteristic_free_central_count k)

end NLS.KdV
