import NLS.KdV.HillL2UpperSquareAsymptotics
import NLS.ComplexAnalysis.UpperCircleReflection

/-! # The physical H_0 coefficient of the actual square on full energy circles -/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate ContDiff
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hillL2RealCutPrimitive_sq_conj
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im ≠ 0) :
    hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (conj z)^2 =
      conj (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) := by
  have hc : (conj z).im ≠ 0 := by simpa only [conj_im, neg_ne_zero] using hz
  have h := hillL2ContinuedPrimitive_conj _ hr z
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz)
  simp only [hillL2RealCutPrimitive, if_neg hz, if_neg hc]
  rw [h, map_pow]
  ring

theorem conj_classicalQuadraticInvariant_of_real (f : ℝ → ℂ) (hf : ∀ x, (f x).im = 0) :
    conj (classicalQuadraticInvariant f) = classicalQuadraticInvariant f := by
  have he : (fun x => (f x)^2) = (fun x => (((f x).re^2 : ℝ) : ℂ)) := by
    funext x
    have hx : f x = ((f x).re : ℂ) := by apply Complex.ext <;> simp [hf x]
    exact (congrArg (fun w : ℂ => w^2) hx).trans (ofReal_pow _ _).symm
  have htwo : conj (2 : ℂ) = 2 := by apply Complex.ext <;> norm_num
  rw [classicalQuadraticInvariant, he, intervalIntegral.integral_ofReal]
  simp only [map_mul, map_div₀, map_one, htwo, conj_ofReal]

theorem classicalQuadraticInvariant_re_eq_half_integral_norm_sq (f : ℝ → ℂ)
    (hf : ∀ x, (f x).im = 0) :
    (classicalQuadraticInvariant f).re = (1/2 : ℝ) * ∫ x in (0 : ℝ)..1, ‖f x‖^2 := by
  have he : (fun x => (f x)^2) = (fun x => ((‖f x‖^2 : ℝ) : ℂ)) := by
    funext x
    have hx : f x = ((f x).re : ℂ) := by apply Complex.ext <;> simp [hf x]
    have hn : ‖f x‖^2 = (f x).re^2 := by rw [Complex.sq_norm, normSq_apply, hf x]; ring
    exact ((congrArg (fun w : ℂ => w^2) hx).trans (ofReal_pow _ _).symm).trans
      (congrArg Complex.ofReal hn.symm)
  rw [classicalQuadraticInvariant, he, intervalIntegral.integral_ofReal]
  norm_num

theorem exists_hillL2Square_circle_quadratic_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∀ w ∈ sphere (0 : ℂ) ((hillFreeBandFrequency n)^2),
        (hillFreeBandFrequency n)^4 *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w ^ 2 + w -
            classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (2*w)‖ ≤ C := by
  let q := hillContinuousCoefficients Q
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let f : ℂ → ℂ := fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2 + w - A/(2*w)
  have hA : conj A = A := conj_classicalQuadraticInvariant_of_real _ (fun x => hreal (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Square_upper_arc_quadratic_remainder Q hq hr hf hp hmean
  refine ⟨C, hC, K, ?_⟩
  intro n hn
  apply weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro w hw hi
    have hnorm : ‖w‖ = (hillFreeBandFrequency n)^2 := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    obtain ⟨t, ht⟩ := exists_upper_circleMap_parameter w _ hnorm hi
    have he : hillFreeUpperFrequency n t ^ 2 = w := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    rw [he] at h
    exact h
  · intro w hw
    dsimp only [f]
    rw [hillL2RealCutPrimitive_sq_conj q hq hr w hw]
    simp only [map_sub, map_add, map_div₀, map_mul, map_ofNat, hA]

end NLS.KdV
