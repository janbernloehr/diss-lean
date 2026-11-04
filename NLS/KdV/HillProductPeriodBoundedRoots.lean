import NLS.KdV.HillProductPeriodMovingDerivativeLimit
import NLS.ComplexAnalysis.CompactParameterBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The original entire omitted product is bounded uniformly in the
omitted index on bounded energy and Hilbert root inputs. -/
theorem norm_hillAbelianHilbertProduct_le_of_bounds
    (n : ℕ) (E : ℂ) (a : Coeff 2) (A T : ℝ) (ha : ‖a‖≤A) (hE : ‖E‖≤T) :
    ‖hillAbelianHilbertProduct n (E,a)‖≤Real.exp ((A+2*T)*‖hillAbelianHilbertWeight 0‖) := by
  have hi : ‖hillAbelianHilbertInput (E,a)‖≤A+2*T := by
    change ‖a-E • Coeff.positivePuncturedLattice 2 (by norm_num)‖≤A+2*T
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    have hh := mul_le_mul_of_nonneg_left Coeff.norm_positivePuncturedLattice_two_le (norm_nonneg E)
    linarith
  have hw : ‖hillAbelianHilbertWeight n‖≤‖hillAbelianHilbertWeight 0‖ := by
    rw [hillAbelianHilbertWeight_eq_delete_full]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro m
    by_cases hm : m=(n : ℤ)
    · subst m
      rw [Coeff.deleteCoordinate_apply_same,norm_zero]
      exact norm_nonneg _
    · rw [Coeff.deleteCoordinate_apply_other _ _ hm]
  exact (norm_hilbertWeightedProduct_le _ _).trans (Real.exp_le_exp.mpr
    ((mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))))

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Each original fixed-contour product period has a common source
neighborhood and a bound for every omitted index and bounded root input. -/
theorem exists_hillAbelianProductComplexPeriod_bounded_roots
    (k : ℕ) (hk : 1≤k) (A : ℝ) :
    ∃ U : Set (Coeff 2), ∃ C : ℝ, IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ 0<C ∧
      (∀ n : ℕ, AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr n k) (univ ×ˢ U)) ∧
      ∀ n : ℕ, ∀ a : Coeff 2, ‖a‖≤A → ∀ p∈U,
        ‖hillAbelianProductComplexPeriod q hq hr n k (a,p)‖≤C := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let D := hillAbelianComplexRootDomain q hq hr
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hi : ContinuousOn (fun v : ℂ × Coeff 2 => (hillAbelianComplexRoot q hq hr v)⁻¹) D := by
    intro v hv
    exact (((analyticOnNhd_hillAbelianComplexRoot q hq hr v hv).inv
      (hillAbelianComplexRoot_ne_zero q hq hr v hv)).continuousAt).continuousWithinAt
  obtain ⟨U,hU,hqU,D0,hD0,hroot⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun v : ℂ × Coeff 2 => (hillAbelianComplexRoot q hq hr v)⁻¹) D
    (isOpen_hillAbelianComplexRootDomain q hq hr) hi (sphere c R) (isCompact_sphere c R)
    (SpectralWeight.one.toCoeff q) (fun E hE => mem_hillAbelianComplexRootDomain_base q hq hr E
      (hillRealGapContour_sphere_subset q hq hr k hk hE))
  let M := Real.exp ((A+2*(‖c‖+R))*‖hillAbelianHilbertWeight 0‖)*(D0+1)
  let C := R*M+1
  have hM : 0≤M := by dsimp only [M];positivity
  have hC : 0<C := by dsimp only [C];positivity
  have hdom (p : Coeff 2) (hp : p∈U) (E : ℂ) (hE : E∈sphere c R) : (E,p)∈D := (hroot p hp E hE).1
  refine ⟨U,C,hU,hqU,hC,(fun n => analyticOnNhd_hillAbelianProductComplexPeriod_of_domain q hq hr n k hk U hU hdom),?_⟩
  intro n a ha p hp
  have hbound (E : ℂ) (hE : E∈sphere c R) :
      ‖hillAbelianHilbertProduct n (E,a)/hillAbelianComplexRoot q hq hr (E,p)‖≤M := by
    have hEc : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
    have hEt : ‖E‖≤‖c‖+R := by have hh := norm_le_norm_sub_add E c;linarith
    rw [div_eq_mul_inv,norm_mul]
    exact mul_le_mul (norm_hillAbelianHilbertProduct_le_of_bounds n E a A (‖c‖+R) ha hEt)
      ((hroot p hp E hE).2.trans (by linarith)) (norm_nonneg _) (by positivity)
  have hh : ‖hillAbelianProductComplexPeriod q hq hr n k (a,p)‖≤R*M := by
    unfold hillAbelianProductComplexPeriod
    rw [norm_mul,norm_inv,norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hR.le hbound)
      (by positivity : 0≤(2*Real.pi)⁻¹)).trans_eq
    field_simp
  exact hh.trans (by dsimp only [C];linarith)

theorem norm_hillScaledProductPeriodCoefficient_le
    (n k : ℕ) (hn : 1≤n) :
    ‖hillScaledProductPeriodCoefficient n k‖≤2*Real.pi+2*|freeHillValue k|/Real.pi := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have h_inv : ‖(n : ℂ)⁻¹‖≤1 := by
    rw [norm_inv,norm_natCast]
    exact inv_le_one_of_one_le₀ hnR
  unfold hillScaledProductPeriodCoefficient
  apply (norm_add_le _ _).trans
  have hterm : ‖(2*(freeHillValue k : ℂ)/(Real.pi : ℂ))*((n : ℂ)⁻¹)^2‖≤2*|freeHillValue k|/Real.pi := by
    rw [norm_mul,norm_pow]
    have hs : ‖(n : ℂ)⁻¹‖^2≤1 := by nlinarith [norm_nonneg ((n : ℂ)⁻¹)]
    apply (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq
    simp only [mul_one,norm_div,norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hfirst : ‖-2*(Real.pi : ℂ)‖=2*Real.pi := by
    simp only [norm_mul,norm_neg,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hfirst]
  linarith only [hterm]

end NLS.KdV
