import NLS.KdV.ClassicalHillWeightedDirichletError
import NLS.KdV.HillL2SmallPotentialTrace
import NLS.KdV.HillL2DirichletCharacteristic
import NLS.ZakharovShabat.FreeSineExteriorBounds

/-! # Actual rough Hill Dirichlet control on the full spectral exterior -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The genuine rough characteristic has one exponential factor and
an inverse-square frequency error; its threshold is independent of Im z. -/
theorem hillL2DirichletCharacteristic_free_error_weighted (q : Coeff 2) (z : ℂ) (hz : z≠0)
    (hsmall : 4*‖q‖≤‖z‖) :
    ‖hillL2DirichletCharacteristic q (z^2)-sin z/z‖≤4*Real.exp |z.im| *‖q‖/‖z‖^2 := by
  have hfinite (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖≤‖q‖) :
      ‖hillL2DirichletCharacteristic (Coeff.ofFinsupp (p := 2) a) (z^2)-sin z/z‖≤
        4*Real.exp |z.im| *‖q‖/‖z‖^2 := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hmass : classicalHillPotentialMass (hillUnitPotentialCurve Q)≤2*‖q‖ := by
      apply (classicalHillPotentialMass_continuous_bound Q).trans
      rw [hq]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    have hnorm : 0<‖z‖ := norm_pos_iff.mpr hz
    have hs : classicalHillPotentialMass (hillUnitPotentialCurve Q)/‖z‖≤1/2 :=
      (div_le_iff₀ hnorm).mpr (by nlinarith)
    rw [← hq,hillL2DirichletCharacteristic_eq_classical]
    apply (classicalHillDirichlet_free_error_weighted (hillUnitPotentialCurve Q) z hz hs).trans
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) (sq_nonneg ‖z‖)).trans_eq
    ring
  have hlim : Tendsto (fun s : Finset ℤ =>
      ‖hillL2DirichletCharacteristic (Coeff.truncate s q) (z^2)-sin z/z‖) atTop
      (𝓝 ‖hillL2DirichletCharacteristic q (z^2)-sin z/z‖) := by
    have hc : Continuous (fun a : Coeff 2 => hillL2DirichletCharacteristic a (z^2)) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      exact ((analyticOnNhd_hillL2DirichletCharacteristic_joint (z^2,a) (mem_univ _)).comp
        (f := fun b : Coeff 2 => (z^2,b)) (analyticAt_const.prod analyticAt_id)).continuousAt
    exact (((hc.tendsto q).comp (Coeff.tendsto_truncate (by simp) q)).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro s
  have ht : Coeff.ofFinsupp (p := 2) (Coeff.finiteRestriction s q)=Coeff.truncate s q :=
    Coeff.ofFinsupp_finiteRestriction s q
  rw [← ht]
  apply hfinite
  rw [ht]
  exact Coeff.norm_truncate_le (by norm_num) s q

/-- Outside fixed free discs, one reciprocal constant works on every
bounded complex L2 potential ball, after a common frequency cutoff. -/
theorem exists_hillL2Dirichlet_exterior_lower_bound {r : ℝ} (hr : 0<r) :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ R : ℝ, 0<R ∧ ∀ q : Coeff 2, ‖q‖≤B → ∀ z : ℂ,
      R≤‖z‖ → (∀ m : ℤ, r≤‖z-(Real.pi : ℂ)*m‖) →
      hillL2DirichletCharacteristic q (z^2)≠0 ∧
        Real.exp |z.im|≤C*‖z‖*‖hillL2DirichletCharacteristic q (z^2)‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_exp_im_div_sin_of_separated hr
  refine ⟨2*C,by positivity,?_⟩
  intro B
  refine ⟨max 1 (max (4*B) (8*C*B)),by positivity,?_⟩
  intro q hq z hz hsep
  have hnorm : 0<‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) ((le_max_left _ _).trans hz)
  have hsmall : 4*‖q‖≤‖z‖ :=
    (mul_le_mul_of_nonneg_left hq (by norm_num)).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hz))
  have hlarge : 8*C*‖q‖≤‖z‖ :=
    (mul_le_mul_of_nonneg_left hq (by positivity)).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hz))
  have hsine := hbound z hsep
  rw [norm_div,norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)] at hsine
  have hsinne := sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep)
  have hs : Real.exp |z.im|≤C*‖sin z‖ := (div_le_iff₀ (norm_pos_iff.mpr hsinne)).mp hsine
  let e := ‖hillL2DirichletCharacteristic q (z^2)-sin z/z‖
  have he := hillL2DirichletCharacteristic_free_error_weighted q z (norm_pos_iff.mp hnorm) hsmall
  change e≤4*Real.exp |z.im| *‖q‖/‖z‖^2 at he
  have he2 := (le_div_iff₀ (sq_pos_of_pos hnorm)).mp he
  have hehalf : 2*C*‖z‖*e≤Real.exp |z.im| := by
    have hm := mul_le_mul_of_nonneg_left he2 hC.le
    have hl := mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg |z.im|)
    nlinarith
  have hn := norm_le_norm_sub_add (sin z/z) (hillL2DirichletCharacteristic q (z^2))
  rw [norm_div,norm_sub_rev] at hn
  change ‖sin z‖/‖z‖≤e+‖hillL2DirichletCharacteristic q (z^2)‖ at hn
  have ht := (div_le_iff₀ hnorm).mp hn
  have hfinal : Real.exp |z.im|≤(2*C)*‖z‖*‖hillL2DirichletCharacteristic q (z^2)‖ := by
    nlinarith [mul_le_mul_of_nonneg_left ht hC.le]
  refine ⟨?_,hfinal⟩
  intro hzero
  rw [hzero,norm_zero,mul_zero] at hfinal
  exact (Real.exp_pos _).not_ge hfinal

end NLS.KdV
