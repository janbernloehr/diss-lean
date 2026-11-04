import NLS.KdV.HillFreeUpperArcs
import NLS.ComplexAnalysis.ConnectedPhaseControl
import NLS.KdV.ClassicalWeightedTraceAsymptotics
import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.ZakharovShabat.NLSHamiltonianPhasePolynomial

/-! # Actual Hill primitive asymptotics on expanding upper energy arcs

The source-normalized primitive is recovered from the actual physical
discriminant. The free band anchor fixes its branch, and connected phase
control propagates the all-order error along the entire closed upper arc.
No primitive expansion or branch identity is supplied as a hypothesis.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

theorem exists_hillL2RealCutPrimitive_upper_arc_error_bound
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
          (hillFreeUpperFrequency n t ^ 2) -
        nlsHamiltonianPhase (fun _ => -1) (fun x => -Q (x : AddCircle (2 : ℝ))) N
          (hillFreeUpperFrequency n t)‖ ≤ C / (2*hillFreeBandFrequency n)^N := by
  let : PreconnectedSpace (Icc (0 : ℝ) Real.pi) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2 : ℝ))
  let q := hillContinuousCoefficients Q
  let A := nlsHamiltonianCorrection (fun _ => -1) (-f) N
  obtain ⟨c, hc, hsinh⟩ := exists_hillFreeUpperFrequency_sinh_lower_bound
  let ε := min 1 (c/4)
  have hε : 0 < ε := lt_min zero_lt_one (by positivity)
  have hεone : ε ≤ 1 := min_le_left _ _
  have hsmall : 4*ε ≤ c := by have h := min_le_right (1 : ℝ) (c/4); dsimp [ε]; linarith
  obtain ⟨C₀, hC₀, herr⟩ := exists_classicalDiscriminant_upper_hamiltonian_error_bound
    (fun _ => -1) (-f) contDiff_const hf.neg (fun _ => rfl)
    (fun x => congrArg Neg.neg (hp x)) N
  have hcurve : scalarPotentialCurve f hf.continuous = hillUnitPotentialCurve Q := by
    ext t
    rfl
  have hD (z : ℂ) : hillL2Discriminant (SpectralWeight.one.toCoeff q) (z^2) =
      classicalDiscriminant (classicalPotentialOfFunctions (fun _ => -1) (-f) continuous_const hf.continuous.neg) z := by
    rw [hillL2Discriminant_eq_classical Q, ← hcurve, classicalHillDiscriminant_sq,
      constantUpperPotential_scalarPotentialCurve]
  have htrace (z : ℂ) (hz : 1 ≤ ‖z‖) (him : 0 ≤ z.im) :
      Real.exp (-z.im) * ‖hillL2Discriminant (SpectralWeight.one.toCoeff q) (z^2) -
        2*cosh (-I*z + A z⁻¹)‖ ≤ C₀/(2*‖z‖)^N := by
    have h := herr z hz him
    have he : 2*cos (I*nlsHamiltonianPhase (fun _ => -1) (-f) N z) =
        2*cosh (-I*z + A z⁻¹) := by
      rw [mul_comm I, cos_mul_I, nlsHamiltonianPhase_eq_correction]
    rw [he, ← hD z] at h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-z.im))
    apply hh.trans_eq
    rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hA : ContinuousAt A 0 := (analyticAt_nlsHamiltonianCorrection _ _ N 0).continuousAt
  obtain ⟨ρ, hρ, hmodel⟩ := Metric.continuousAt_iff.mp hA (ε/4) (by positivity)
  have hinv : Tendsto (fun n => (hillFreeBandFrequency n)⁻¹) atTop (𝓝 0) :=
    tendsto_hillFreeBandFrequency.inv_tendsto_atTop
  have hinv₂ : Tendsto (fun n => (2*hillFreeBandFrequency n)⁻¹) atTop (𝓝 0) :=
    (tendsto_hillFreeBandFrequency.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).inv_tendsto_atTop
  have herror : Tendsto (fun n => C₀/(2*hillFreeBandFrequency n)^N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by omega : N ≠ 0), mul_zero] using (hinv₂.pow N).const_mul C₀
  have hanchor : Tendsto (fun n => ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
      ((freeCosineZero n)^2) + I*freeCosineZero n‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (tendsto_hillL2RealCutPrimitive_free_band_correction q hq hr).norm
  refine ⟨C₀/c, by positivity, ?_⟩
  have heventual : ∀ᶠ n : ℕ in atTop, ∀ t : Icc (0 : ℝ) Real.pi,
      ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (hillFreeUpperFrequency n t ^ 2) -
        nlsHamiltonianPhase (fun _ => -1) (-f) N (hillFreeUpperFrequency n t)‖ ≤
          (C₀/c)/(2*hillFreeBandFrequency n)^N := by
    filter_upwards [tendsto_hillFreeBandFrequency.eventually_ge_atTop 1,
      hinv.eventually (gt_mem_nhds hρ),
      herror.eventually (gt_mem_nhds (by positivity : 0 < c*ε/4)),
      hanchor.eventually (gt_mem_nhds hε)] with n hn hρn herrn hanchorn
    let z : Icc (0 : ℝ) Real.pi → ℂ := fun t => hillFreeUpperFrequency n t
    let a : Icc (0 : ℝ) Real.pi → ℂ := fun t => -I*z t
    let u : Icc (0 : ℝ) Real.pi → ℂ := fun t =>
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (z t ^ 2) + I*z t
    let v : Icc (0 : ℝ) Real.pi → ℂ := fun t => A (z t)⁻¹
    have hu : Continuous u := (continuous_hillL2FreeUpperArcPrimitive q hq hr n).add
      (continuous_const.mul ((continuous_hillFreeUpperFrequency n).comp continuous_subtype_val))
    have hv (t : Icc (0 : ℝ) Real.pi) : ‖v t‖ ≤ ε/4 := by
      have hw : dist ((z t)⁻¹) (0 : ℂ) < ρ := by
        rw [dist_zero_right, norm_inv, norm_hillFreeUpperFrequency]
        exact hρn
      have hh := hmodel hw
      have hvlt : ‖v t‖ < ε/4 := by
        simpa only [v, A, nlsHamiltonianCorrection_zero, dist_zero_right] using hh
      exact hvlt.le
    have ha (t : Icc (0 : ℝ) Real.pi) : 0 ≤ (a t).re := by
      dsimp [a]
      simpa [mul_re] using hillFreeUpperFrequency_im_nonneg n t t.property
    have hau (t : Icc (0 : ℝ) Real.pi) : a t+u t =
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (z t ^ 2) := by dsimp [a, u]; ring
    have htv (t : Icc (0 : ℝ) Real.pi) :
        Real.exp (-(a t).re) * ‖2*cosh (a t+u t) - 2*cosh (a t+v t)‖ ≤ c*ε/4 := by
      rw [hau, hillL2RealCutPrimitive_trace q hq hr]
      have hh := htrace (z t) (by rw [norm_hillFreeUpperFrequency]; exact hn)
        (hillFreeUpperFrequency_im_nonneg n t t.property)
      have hnorm : ‖z t‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
      change Real.exp (-(-I*z t).re) * ‖hillL2Discriminant (SpectralWeight.one.toCoeff q) (z t ^ 2) -
        2*cosh (-I*z t + A (z t)⁻¹)‖ ≤ _
      rw [show (-I*z t).re = (z t).im by simp [mul_re]]
      exact hh.trans (by rw [hnorm]; exact herrn.le)
    let t₀ : Icc (0 : ℝ) Real.pi := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
    have hu₀ : ‖u t₀‖ < ε := by
      simpa only [u, z, t₀, hillFreeUpperFrequency_zero] using hanchorn
    have hall := cosh_phase_control_of_anchor a u v hu c ε hc hε hεone hsmall ha
      (fun t => hsinh n t t.property) hv htv t₀ hu₀
    intro t
    have hh := (hall t).2
    rw [hau, hillL2RealCutPrimitive_trace q hq hr] at hh
    have he : u t-v t = hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (z t ^ 2) -
        nlsHamiltonianPhase (fun _ => -1) (-f) N (z t) := by
      rw [nlsHamiltonianPhase_eq_correction]
      dsimp [u, v, A]
      ring
    rw [he] at hh
    apply hh.trans
    have h := div_le_div_of_nonneg_right
      (htrace (z t) (by rw [norm_hillFreeUpperFrequency]; exact hn)
        (hillFreeUpperFrequency_im_nonneg n t t.property)) hc.le
    change Real.exp (-(-I*z t).re) / c *
      ‖hillL2Discriminant (SpectralWeight.one.toCoeff q) (z t ^ 2) -
        2*cosh (-I*z t + A (z t)⁻¹)‖ ≤ _
    rw [div_mul_eq_mul_div, show (-I*z t).re = (z t).im by simp [mul_re]]
    have hnorm : ‖z t‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
    rw [hnorm] at h
    exact h.trans_eq (by ring)
  exact Filter.eventually_atTop.mp heventual

/-- The actual primitive has the independently computed physical H_0 and
KdV energy terms, with higher phase terms and a strictly higher-order
remainder retained explicitly. -/
theorem exists_hillL2RealCutPrimitive_upper_arc_physical_error_bound
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2) +
        I * (z - classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (4*z^3) -
          classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (16*z^5) -
          ∑ j ∈ Finset.range M,
            classicalNLSHamiltonian (fun _ => -1) (fun x => -Q (x : AddCircle (2 : ℝ))) (j+6) /
              (2*z)^(j+6))‖ ≤ C / (2*hillFreeBandFrequency n)^(M+5) := by
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2RealCutPrimitive_upper_arc_error_bound Q hq hr hf hp
    (M+5) (by omega)
  refine ⟨C, hC, K, ?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  have hz : z ≠ 0 := norm_pos_iff.mp (by rw [norm_hillFreeUpperFrequency]; exact hillFreeBandFrequency_pos n)
  have hphase := phase_const_upper_extended (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) hf hp hmean M z hz
  rw [show -(fun x : ℝ => Q (x : AddCircle (2 : ℝ))) =
    (fun x : ℝ => -Q (x : AddCircle (2 : ℝ))) from rfl] at hphase
  have hh := hbound n hn t
  have heq : hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2) +
      I * (z - classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (4*z^3) -
        classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (16*z^5) -
        ∑ j ∈ Finset.range M,
          classicalNLSHamiltonian (fun _ => -1) (fun x => -Q (x : AddCircle (2 : ℝ))) (j+6) /
            (2*z)^(j+6)) =
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2) -
        nlsHamiltonianPhase (fun _ => -1) (fun x => -Q (x : AddCircle (2 : ℝ))) (M+5) z := by
    rw [← hphase, ← mul_assoc, I_mul_I, neg_one_mul]
    ring
  dsimp only
  rw [heq]
  exact hh

end NLS.KdV
