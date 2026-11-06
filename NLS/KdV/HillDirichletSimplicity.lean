import NLS.KdV.HillDirichletLagrange
import NLS.ComplexAnalysis.QuadraticPuncturedLimit
import Mathlib.Analysis.Analytic.Order

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem hillL2Dirichlet_derivative_normalization
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy=0) :
    deriv (hillL2DirichletCharacteristic q) energy*
      (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1) ⟨1,by norm_num⟩).2 =
      (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) : ℂ) := by
  let z := Complex.sqrt energy
  let A := hillL2FrequencyStateCurve q z (0,1)
  let g : ℂ := (A ⟨1,by norm_num⟩).2
  have hs : z^2=energy := NLS.ComplexAnalysis.complex_sqrt_sq _
  have hpoint (w : ℂ) : (hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).1=
      hillL2DirichletCharacteristic q (w^2) := by
    simpa only [hillL2FrequencyStateCurve_apply,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero,hillL2FrequencyDirichlet] using!
        (hillL2DirichletCharacteristic_sq q w).symm
  have hA0 : (A ⟨1,by norm_num⟩).1=0 := by
    dsimp only [A]
    rw [hpoint,hs,hzero]
  have hcross : Continuous (fun w : ℂ => scalarStateCrossMass A (hillL2FrequencyStateCurve q w (0,1))) := by
    convert! continuous_scalarStateCrossMass.comp
      (continuous_const.prodMk (continuous_hillL2FrequencyStateCurve_frequency q (0,1))) using 1
  have hquad : Tendsto (fun w : ℂ => w^2) (𝓝[≠] z) (𝓝[≠] energy) := by
    simpa only [hs] using tendsto_sq_punctured z
  have hd := (analyticOnNhd_hillL2DirichletCharacteristic q energy (mem_univ _)).differentiableAt.hasDerivAt
  have ht := (hd.tendsto_slope.comp hquad).mul_const g
  have hevent : ∀ᶠ w in 𝓝[≠] z, scalarStateCrossMass A (hillL2FrequencyStateCurve q w (0,1)) =
      slope (hillL2DirichletCharacteristic q) energy (w^2)*g := by
    have he := (tendsto_nhdsWithin_iff.mp hquad).2
    filter_upwards [he] with w hw
    simp only [mem_compl_iff,mem_singleton_iff] at hw
    have hL := hillL2FrequencyStateCurve_lagrange_identity q z w
    change (z^2-w^2)*scalarStateCrossMass A (hillL2FrequencyStateCurve q w (0,1)) =
      (A ⟨1,by norm_num⟩).1*(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).2-
      g*(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).1 at hL
    rw [hs,hA0,zero_mul,zero_sub,hpoint] at hL
    rw [slope_def_field,hzero,sub_zero,div_mul_eq_mul_div]
    apply (eq_div_iff (sub_ne_zero.mpr hw)).mpr
    linear_combination -hL
  have hleft : Tendsto (fun w : ℂ => scalarStateCrossMass A (hillL2FrequencyStateCurve q w (0,1)))
      (𝓝[≠] z) (𝓝 (scalarStateCrossMass A A)) :=
    hcross.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun w : ℂ => scalarStateCrossMass A (hillL2FrequencyStateCurve q w (0,1))) =ᶠ[𝓝[≠] z]
      (fun w : ℂ => slope (hillL2DirichletCharacteristic q) energy (w^2)*g) := hevent
  have hlim := tendsto_nhds_unique hleft (ht.congr' heq.symm)
  have hreal : ∀ t, (A t).1.im=0 := by
    intro t
    exact (hillL2FrequencyStateCurve_real q hq z
      (by rw [hs]; exact hillL2DirichletCharacteristic_zero_real q hq energy hzero) (0,1) (by norm_num) t).1
  rw [scalarStateCrossMass_self_real A hreal] at hlim
  exact hlim.symm

theorem hillL2DirichletCharacteristic_deriv_ne_zero
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) : deriv (hillL2DirichletCharacteristic q) energy≠0 := by
  intro he
  have h := hillL2Dirichlet_derivative_normalization q hq energy hz
  rw [he,zero_mul] at h
  have hm := hillL2FrequencyStateCurve_mass_pos q (Complex.sqrt energy) (0,1)
    (by intro hzero; have hh := congrArg Prod.snd hzero; norm_num at hh)
  have hh : scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))=0 := by
    exact Complex.ofReal_eq_zero.mp h.symm
  linarith

theorem analyticOrderAt_hillL2Dirichlet_zero (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) :
    analyticOrderAt (hillL2DirichletCharacteristic q) energy=1 :=
  (analyticOnNhd_hillL2DirichletCharacteristic q energy (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hz (hillL2DirichletCharacteristic_deriv_ne_zero q hq energy hz)

theorem analyticOrderNatAt_hillL2Dirichlet_zero (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) :
    analyticOrderNatAt (hillL2DirichletCharacteristic q) energy=1 := by
  simp only [analyticOrderNatAt,analyticOrderAt_hillL2Dirichlet_zero q hq energy hz]
  norm_num

end NLS.KdV
