import NLS.ZakharovShabat.CentralCircleThresholds
import NLS.KdV.HillL2WeightedDirichletError
import NLS.KdV.HillGapNumeratorDecay
import NLS.ZakharovShabat.FreeSineExteriorBounds
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillL2DirichletCharacteristic_relative_error_weighted
    (q : Coeff 2) (z : ℂ) (hz : z≠0) (hs : sin z≠0)
    (hsmall : 4*‖q‖≤‖z‖) (C : ℝ)
    (hC : ‖(Real.exp |z.im| : ℂ)/sin z‖≤C) :
    ‖hillL2DirichletCharacteristic q (z^2)/(sin z/z)-1‖≤4*C*‖q‖/‖z‖ := by
  have hfree : sin z/z≠0 := div_ne_zero hs hz
  have hnz : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hns : ‖sin z‖≠0 := norm_ne_zero_iff.mpr hs
  rw [show hillL2DirichletCharacteristic q (z^2)/(sin z/z)-1=
    (hillL2DirichletCharacteristic q (z^2)-sin z/z)/(sin z/z) by field_simp,
    norm_div]
  calc
    _ ≤ (4*Real.exp |z.im| *‖q‖/‖z‖^2)/‖sin z/z‖ :=
      div_le_div_of_nonneg_right (hillL2DirichletCharacteristic_free_error_weighted_of_density q z hz hsmall) (norm_nonneg _)
    _ = (4*‖q‖/‖z‖)*‖(Real.exp |z.im| : ℂ)/sin z‖ := by
      rw [norm_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      field_simp
    _ ≤ (4*‖q‖/‖z‖)*C := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by ring

/-- On expanding central frequency circles, the original rough Hill
Dirichlet characteristic is uniformly close to the free characteristic,
with one cutoff for every source in a prescribed coefficient ball. -/
theorem exists_hillDirichletCharacteristic_central_relative_bounds (B : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ q : Coeff 2, ‖q‖≤B →
      ∀ z∈sphere (0 : ℂ) (centralCircleRadius k),
        hillL2DirichletCharacteristic q (z^2)≠0 ∧
        ‖hillL2DirichletCharacteristic q (z^2)/(sin z/z)-1‖≤1/2 ∧
        ‖(sin z/z)/hillL2DirichletCharacteristic q (z^2)‖≤2 := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_exp_im_div_sin_of_separated (by positivity : 0<Real.pi/4)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (tendsto_centralCircleRadius_atTop.eventually_ge_atTop (max (4*B) (8*C*B)))
  refine ⟨K,?_⟩
  intro k hk q hq z hz
  have hnorm : ‖z‖=centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hzpos : 0<‖z‖ := by rw [hnorm];exact centralCircleRadius_pos k
  have hz0 : z≠0 := norm_pos_iff.mp hzpos
  have hsep (n : ℤ) : Real.pi/4≤‖z-(Real.pi : ℂ)*n‖ := by
    have hh := centralCircle_lattice_gap k hz n
    linarith [Real.pi_pos]
  have hs : sin z≠0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsep)
  have hsmall : 4*‖q‖≤‖z‖ := by
    have hh := (le_max_left (4*B) (8*C*B)).trans (hK k hk)
    rw [← hnorm] at hh
    linarith
  have hr := hillL2DirichletCharacteristic_relative_error_weighted q z hz0 hs hsmall C (hbound z hsep)
  have hhalf : 4*C*‖q‖/‖z‖≤1/2 := by
    apply (div_le_iff₀ hzpos).mpr
    have hh := (le_max_right (4*B) (8*C*B)).trans (hK k hk)
    rw [← hnorm] at hh
    nlinarith [mul_le_mul_of_nonneg_left hq hC.le]
  have herr := hr.trans hhalf
  have hfree : sin z/z≠0 := div_ne_zero hs hz0
  have hlow : (1 : ℝ)/2≤‖hillL2DirichletCharacteristic q (z^2)/(sin z/z)‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (hillL2DirichletCharacteristic q (z^2)/(sin z/z))
    rw [norm_one,norm_sub_rev] at hh
    linarith
  have hD : hillL2DirichletCharacteristic q (z^2)≠0 := by
    intro hh
    rw [hh,zero_div,norm_zero] at hlow
    norm_num at hlow
  refine ⟨hD,herr,?_⟩
  rw [show (sin z/z)/hillL2DirichletCharacteristic q (z^2)=
    (hillL2DirichletCharacteristic q (z^2)/(sin z/z))⁻¹ by field_simp]
  rw [norm_inv,inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0<‖hillL2DirichletCharacteristic q (z^2)/(sin z/z)‖)).mpr (by linarith)

theorem exists_hillDirichletCharacteristic_energy_central_bounds (B : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ q : Coeff 2, ‖q‖≤B →
      ∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
        hillL2DirichletCharacteristic q E≠0 ∧
        ‖(sin (Complex.sqrt E)/Complex.sqrt E)/hillL2DirichletCharacteristic q E‖≤2 := by
  obtain ⟨K,hK⟩ := exists_hillDirichletCharacteristic_central_relative_bounds B
  refine ⟨K,?_⟩
  intro k hk q hq E hE
  have hnorm : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hz : Complex.sqrt E∈sphere (0 : ℂ) (centralCircleRadius k) := by
    have hh := congrArg norm (complex_sqrt_sq E)
    rw [norm_pow,hnorm] at hh
    rw [mem_sphere,dist_zero_right]
    nlinarith [norm_nonneg (Complex.sqrt E),centralCircleRadius_pos k]
  have hh := hK k hk q hq (Complex.sqrt E) hz
  rw [complex_sqrt_sq] at hh
  exact ⟨hh.1,hh.2.2⟩

end NLS.KdV
