import NLS.ZakharovShabat.SourceSobolevDiscriminantUniform
import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Uniform spectral derivative of the discriminant error

Analyticity away from zero and a fixed-radius Cauchy estimate preserve the inverse-frequency order without requiring an extra source derivative.
-/

noncomputable section
open Set Complex Metric NLS.Fourier
namespace NLS.ZakharovShabat

/-- The actual finite Sobolev Hamiltonian phase is analytic away from zero
in the spectral parameter. -/
theorem analyticAt_sobolevHamiltonianPhase_spectral
    (s N : ℕ) (hNs : N ≤ s) (ab : SobolevSource s) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (sobolevHamiltonianPhase s N hNs ab) z := by
  apply (analyticAt_const.mul analyticAt_id).add
  have h (k : Fin N) : AnalyticAt ℂ
      (fun w : ℂ => I*sobolevNLSHamiltonian s ab (k.val+1) (by omega)/(2*w)^(k.val+1)) z :=
    analyticAt_const.div ((analyticAt_const.mul analyticAt_id).pow (k.val+1))
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hz))
  exact Finset.analyticAt_fun_sum Finset.univ (fun k _ => h k)

/-- The intrinsic discriminant error is analytic at each nonzero spectral point,
also for nonsmooth complex Sobolev sources. -/
theorem analyticAt_sourceSobolevDiscriminant_error
    (s N : ℕ) (hNs : N ≤ s) (ab : SobolevSource s) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w =>
      canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) w-
      2*cos (I*sobolevHamiltonianPhase s N hNs ab w)) z := by
  have hd : AnalyticAt ℂ (fun w =>
      canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) w) z :=
    (analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by norm_num) (by norm_num)
      (z,higherSobolevSourceInclusion s ab) (mem_univ _)).comp
      (f := fun w : ℂ => (w,higherSobolevSourceInclusion s ab))
      (analyticAt_id.prod analyticAt_const)
  exact hd.sub (analyticAt_const.mul
    (Complex.analyticAt_cos.comp
      (analyticAt_const.mul (analyticAt_sobolevHamiltonianPhase_spectral s N hNs ab z hz))))

/-- A fixed-radius Cauchy estimate preserves the uniform inverse-frequency
order for the spectral derivative of the actual discriminant error. -/
theorem exists_uniform_sourceSobolevDiscriminant_derivative_strip_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ∀ z : ℂ, 2 ≤ ‖z‖ → |z.im| ≤ H →
        ‖deriv (fun w =>
          canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) w-
          2*cos (I*sobolevHamiltonianPhase s N hNs ab w)) z‖ ≤ C/‖z‖^N := by
  obtain ⟨C,hC,h⟩ := exists_uniform_sourceSobolevDiscriminant_hamiltonian_strip_error_bound
    s N hs hNs R hR (H+1)
  refine ⟨4*C,by positivity,?_⟩
  intro ab hab z hz hzH
  let f : ℂ → ℂ := fun w =>
    canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) w-
    2*cos (I*sobolevHamiltonianPhase s N hNs ab w)
  have hgeom (w : ℂ) (hw : w ∈ ball z (1/2+1/2)) :
      1 ≤ ‖w‖ ∧ ‖z‖ ≤ 2*‖w‖ ∧ |w.im| ≤ H+1 := by
    have hd : ‖w-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm,show (1:ℝ)/2+1/2=1 by norm_num] using hw
    have hn := norm_le_norm_add_norm_sub w z
    have hn' : ‖z-w‖ = ‖w-z‖ := norm_sub_rev z w
    have hi := abs_im_le_norm (w-z)
    have ht := abs_add_le (w.im-z.im) z.im
    simp only [sub_im] at hi
    rw [sub_add_cancel] at ht
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  have hf : DifferentiableOn ℂ f (ball z (1/2+1/2)) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro he
      have := (hgeom w hw).1
      norm_num [he] at this
    exact (analyticAt_sourceSobolevDiscriminant_error s N hNs ab w hw0).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ ball z (1/2+1/2), ‖f w‖ ≤ C/‖z‖^N := by
    intro w hw
    obtain ⟨hwn,hwz,hwH⟩ := hgeom w hw
    apply (h ab hab w hwn hwH).trans
    gcongr
  have hd := NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound
    f z z (1/2) (1/2) (C/‖z‖^N) (by norm_num) hf hb (by simp)
  rw [norm_deriv_eq_norm_fderiv]
  convert hd using 1; ring

end NLS.ZakharovShabat
