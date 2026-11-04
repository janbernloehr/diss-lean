import NLS.KdV.HillL2UpperArcAsymptotics
import NLS.ComplexAnalysis.LaurentSquareRemainder

/-! # The actual physical H_0 coefficient in the squared primitive on upper arcs -/

noncomputable section
open scoped ContDiff
open Set Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem exists_hillL2Square_upper_arc_quadratic_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^4 *
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)^2 + z^2 -
          classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (2*z^2)‖ ≤ C := by
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let B := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let a := I*A/4
  let b := I*B/16
  obtain ⟨D, hD, K, hb⟩ := exists_hillL2RealCutPrimitive_upper_arc_physical_error_bound Q hq hr hf hp hmean 0
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  let C := D*(2*(1+‖a‖+‖b‖)+D) + 2*‖b‖+‖a‖^2+2*‖a‖*‖b‖+‖b‖^2
  refine ⟨C+1, by dsimp [C]; positivity, max K K₁, ?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hnorm : ‖z‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
  have hz1 : 1 ≤ ‖z‖ := by rw [hnorm]; exact hK₁ n (by omega)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have h := hb n (by omega) t
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add] at h
  have heq : F+I*(z-A/(4*z^3)-B/(16*z^5)) = F-(-I*z+a/z^3+b/z^5) := by
    dsimp [a, b]
    field_simp
    ring
  change ‖F+I*(z-A/(4*z^3)-B/(16*z^5))‖ ≤ D/(2*hillFreeBandFrequency n)^5 at h
  rw [heq, ← hnorm] at h
  have herror : ‖z‖^5 * ‖F-(-I*z+a/z^3+b/z^5)‖ ≤ D := by
    have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg z) 5)
    have he : ‖z‖^5 * (D/(2*‖z‖)^5) = D/32 := by
      field_simp
      ring
    exact hh.trans (he ▸ (by linarith : D/32 ≤ D))
  have hs := norm_square_laurent_error_of_phase_error z F a b D hz1 hD.le herror
  have hcoef : (2*I*a)/z^2 = -A/(2*z^2) := by
    dsimp [a]
    field_simp
    ring_nf
    simp [I_sq]
  rw [hcoef, neg_div, ← sub_eq_add_neg] at hs
  dsimp only
  rw [← hnorm]
  exact hs.trans (by dsimp [C]; linarith)

end NLS.KdV
