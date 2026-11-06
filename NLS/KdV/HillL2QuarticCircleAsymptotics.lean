import NLS.KdV.HillL2UpperQuarticAsymptotics
import NLS.KdV.HillL2SquareCircleAsymptotics

/-! # The physical energy coefficient of the actual quartic primitive on full circles -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate ContDiff
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem conj_classicalHamiltonian_of_real (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hreal : ∀ x, (f x).im = 0) : conj (classicalHamiltonian f) = classicalHamiltonian f := by
  have hg : Differentiable ℝ (fun x => (f x).re) := by fun_prop
  have he : (fun x => ((f x).re : ℂ)) = f := by
    funext x
    apply Complex.ext <;> simp [hreal x]
  have hh := classicalHamiltonian_ofReal (fun x => (f x).re) hg
  rw [he] at hh
  rw [hh,conj_ofReal]

theorem hillL2RealCutPrimitive_fourth_conj
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im ≠ 0) :
    hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (conj z)^4 =
      conj (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 4) := by
  have hh := congrArg (fun w : ℂ => w^2) (hillL2RealCutPrimitive_sq_conj q hq hr z hz)
  simpa only [←map_pow,←pow_mul] using hh

theorem exists_hillL2Quartic_circle_energy_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∀ w ∈ sphere (0 : ℂ) ((hillFreeBandFrequency n)^2),
        (hillFreeBandFrequency n)^3 *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w ^ 4 - w^2 +
            classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) + classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (4*w)‖ ≤ C := by
  let q := hillContinuousCoefficients Q
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let H := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let f : ℂ → ℂ := fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4-w^2+A+H/(4*w)
  have hA : conj A = A := conj_classicalQuadraticInvariant_of_real _ (fun x => hreal (x : AddCircle (2 : ℝ)))
  have hH : conj H = H := conj_classicalHamiltonian_of_real _
    (hf.differentiable (by simp)) (fun x => hreal (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Quartic_upper_arc_energy_remainder Q hq hr hf hp hmean
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  apply weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro w hw hi
    have hnorm : ‖w‖ = (hillFreeBandFrequency n)^2 := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    obtain ⟨t, ht⟩ := exists_upper_circleMap_parameter w _ hnorm hi
    have he : hillFreeUpperFrequency n t ^ 2 = w := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    rw [show hillFreeUpperFrequency n t ^ 4 = (hillFreeUpperFrequency n t ^ 2)^2 by ring,he] at h
    exact h
  · intro w hw
    dsimp only [f]
    rw [hillL2RealCutPrimitive_fourth_conj q hq hr w hw]
    simp only [map_sub, map_add, map_div₀, map_mul, map_ofNat, hA,hH,map_pow]

end NLS.KdV
