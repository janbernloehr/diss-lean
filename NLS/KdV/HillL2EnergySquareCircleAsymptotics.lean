import NLS.KdV.HillL2UpperEnergySquareAsymptotics
import NLS.KdV.HillL2SquareCircleAsymptotics

/-! # Physical energy reality and the full-circle squared-primitive error -/

noncomputable section
open scoped ContDiff ComplexConjugate
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem deriv_im_eq_zero_of_real (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hreal : ∀ x, (f x).im = 0) (x : ℝ) : (deriv f x).im = 0 := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x).hasDerivAt
  have he : (fun u => (f u).im) = fun _ => (0 : ℝ) := funext hreal
  apply hd.unique
  simpa only [Function.comp_def, Complex.imCLM_apply, he] using hasDerivAt_const x (0 : ℝ)

theorem conj_classicalHamiltonian_of_real (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hreal : ∀ x, (f x).im = 0) : conj (classicalHamiltonian f) = classicalHamiltonian f := by
  have hc (x : ℝ) : conj (f x) = f x := by apply Complex.ext <;> simp [hreal x]
  have hdc (x : ℝ) : conj (deriv f x) = deriv f x := by
    apply Complex.ext <;> simp [deriv_im_eq_zero_of_real f hf hreal x]
  have htwo : conj (2 : ℂ) = 2 := by apply Complex.ext <;> norm_num
  rw [classicalHamiltonian, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  funext x
  simp only [map_add, map_div₀, map_pow, hc, hdc, htwo]

theorem exists_hillL2Square_circle_energy_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∀ w ∈ sphere (0 : ℂ) ((hillFreeBandFrequency n)^2),
        (hillFreeBandFrequency n)^5 *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w ^ 2 + w -
            classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (2*w) -
            classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (8*w^2)‖ ≤ C := by
  let q := hillContinuousCoefficients Q
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let B := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let f : ℂ → ℂ := fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2 + w - A/(2*w)-B/(8*w^2)
  have hA : conj A = A := conj_classicalQuadraticInvariant_of_real _ (fun x => hreal (x : AddCircle (2 : ℝ)))
  have hB : conj B = B := conj_classicalHamiltonian_of_real _
    (hf.differentiable (by simp)) (fun x => hreal (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Square_upper_arc_energy_remainder Q hq hr hf hp hmean
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  apply weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro w hw hi
    have hnorm : ‖w‖ = (hillFreeBandFrequency n)^2 := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    obtain ⟨t, ht⟩ := exists_upper_circleMap_parameter w _ hnorm hi
    have he : hillFreeUpperFrequency n t ^ 2 = w := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    rw [show hillFreeUpperFrequency n t ^ 4 = (hillFreeUpperFrequency n t ^ 2)^2 by ring, he] at h
    exact h
  · intro w hw
    dsimp only [f]
    rw [hillL2RealCutPrimitive_sq_conj q hq hr w hw]
    simp only [map_sub, map_add, map_div₀, map_mul, map_ofNat, map_pow, hA, hB]



end NLS.KdV
