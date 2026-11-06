import NLS.KdV.HillProductPeriodParameterLimit
import NLS.ComplexAnalysis.BanachHolomorphicC1

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The exact scalar multiplying the actual omitted product period in
the original scaled differential period. -/
def hillScaledProductPeriodCoefficient (n k : ℕ) : ℂ :=
  -2*(Real.pi : ℂ)+(2*(freeHillValue k : ℂ)/(Real.pi : ℂ))*((n : ℂ)⁻¹)^2

theorem tendsto_hillScaledProductPeriodCoefficient (k : ℕ) :
    Tendsto (fun n : ℕ => hillScaledProductPeriodCoefficient n k) atTop (𝓝 (-2*(Real.pi : ℂ))) := by
  have hinvReal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ofReal_inv,ofReal_natCast,ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp hinvReal
  simpa only [hillScaledProductPeriodCoefficient,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,add_zero] using
    (hc.pow 2).const_mul (2*(freeHillValue k : ℂ)/(Real.pi : ℂ)) |>.const_add (-2*(Real.pi : ℂ))

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem scaled_hillAbelianComplexPeriod_eq_productPeriod
    (n k : ℕ) (hn : 1≤n) (t : Coeff 2 × Coeff 2) :
    (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianComplexPeriod q hq hr n k t=
      hillScaledProductPeriodCoefficient n k*hillAbelianProductComplexPeriod q hq hr n k t := by
  have hn0 : (n : ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hp0 : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfree : (freeHillValue n : ℂ)=(Real.pi : ℂ)^2*(n : ℂ)^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    rfl
  have he : hillScaledProductPeriodCoefficient n k*((n : ℂ)*Real.pi/2)=
      ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ) := by
    rw [hillScaledProductPeriodCoefficient,hfree]
    field_simp
    ring
  rw [hillAbelianProductComplexPeriod_eq_rescaled q hq hr n k hn,←mul_assoc,he]

/-- The whole actual period root derivative row converges in operator
norm along bounded norm-convergent roots and escaping deleted indices. -/
theorem tendsto_hillAbelianProductComplexPeriod_full_root_derivative_of_tendsto
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) (hn : ∀ i, 1≤n i) (hni : Tendsto n l atTop)
    (k : ℕ) (hk : 1≤k) (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0))
    (B : ℝ) (hB : 0≤B) (hab : ∀ i, ‖a i‖≤B) :
    Tendsto (fun i => fderiv ℂ (fun b : Coeff 2 =>
      hillAbelianProductComplexPeriod q hq hr (n i) k (b,SpectralWeight.one.toCoeff q)) (a i)) l
      (𝓝 (fderiv ℂ (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a0)) := by
  obtain ⟨U,C,_,hqU,_,hbound⟩ :=
    exists_hillAbelianProductComplexPeriod_full_root_derivative_uniform_bound q hq hr k hk B hB
  let P : Coeff 2 → ℂ := fun b => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)
  obtain ⟨V,D,_,hqV,_,hA,_⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk 0 (by norm_num)
  have hP : AnalyticOnNhd ℂ P univ := by
    intro b _
    exact (hA 0 (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqV⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hcont : Continuous (fderiv ℂ P) := by
    exact continuousOn_univ.mp ((hP.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen isOpen_univ (by norm_num))
  have hlim := hcont.continuousAt.tendsto.comp ha
  have hzero : Tendsto (fun i => fderiv ℂ (fun b : Coeff 2 =>
      hillAbelianProductComplexPeriod q hq hr (n i) k (b,SpectralWeight.one.toCoeff q)) (a i)-fderiv ℂ P (a i)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun i => norm_nonneg _) _
      (((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).const_div_atTop C).comp hni)
    intro i
    exact hbound (n i) (hn i) (a i) (hab i) _ hqU
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hzero.add hlim

end NLS.KdV
