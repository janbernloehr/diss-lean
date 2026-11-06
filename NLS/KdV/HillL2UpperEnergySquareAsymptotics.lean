import NLS.KdV.HillL2UpperArcAsymptotics
import NLS.ComplexAnalysis.WeightedSquareRemainder

/-! # The actual physical energy coefficient on upper energy arcs -/

noncomputable section
open scoped ContDiff
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis NLS.ZakharovShabat

theorem exists_hillL2Square_upper_arc_energy_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^5 *
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)^2 + z^2 -
          classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (2*z^2) -
          classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (8*z^4)‖ ≤ C := by
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let B := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let H := classicalNLSHamiltonian (fun _ => -1) (fun x : ℝ => -Q (x : AddCircle (2 : ℝ))) 6
  let a := I*A/4
  let b := I*B/16
  obtain ⟨D, hD, K, hb⟩ := exists_hillL2RealCutPrimitive_upper_arc_physical_error_bound Q hq hr hf hp hmean 1
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  let D' := D+‖H‖
  let C := D'*(2*(1+‖a‖+‖b‖)+D')+‖a‖^2+2*‖a‖*‖b‖+‖b‖^2
  refine ⟨C+1, by dsimp [C,D']; positivity, max K K₁, ?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let P := -I*z+a/z^3+b/z^5
  let E := I*H/(2*z)^6
  have hnorm : ‖z‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
  have hz1 : 1 ≤ ‖z‖ := by rw [hnorm]; exact hK₁ n (by omega)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have h := hb n (by omega) t
  simp only [Finset.sum_range_one, zero_add] at h
  have heq : F+I*(z-A/(4*z^3)-B/(16*z^5)-H/(2*z)^6) = (F-P)-E := by
    dsimp only [P,a,b,E]
    field_simp
    ring
  change ‖F+I*(z-A/(4*z^3)-B/(16*z^5)-H/(2*z)^6)‖ ≤ D/(2*hillFreeBandFrequency n)^6 at h
  rw [heq, ← hnorm] at h
  have hfirst : ‖z‖^6 * ‖(F-P)-E‖ ≤ D := by
    have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg z) 6)
    have he : ‖z‖^6 * (D/(2*‖z‖)^6) = D/64 := by field_simp; ring
    exact hh.trans (he ▸ (by linarith : D/64 ≤ D))
  have hnorm2 : ‖(2 : ℂ)*z‖ = 2*‖z‖ := by rw [norm_mul]; norm_num
  have h2z : 1 ≤ ‖(2 : ℂ)*z‖ := by rw [hnorm2]; linarith
  have hH : (2*‖z‖)^6 * ‖E‖ ≤ ‖H‖ := by
    simpa only [hnorm2, norm_mul, norm_I, one_mul] using
      norm_weighted_laurent_term_le (2*z) (I*H) h2z 6 6 le_rfl
  have hE : ‖z‖^6 * ‖E‖ ≤ ‖H‖ := by nlinarith [mul_nonneg (pow_nonneg (norm_nonneg z) 6) (norm_nonneg E)]
  have herror : ‖z‖^6 * ‖F-P‖ ≤ D' := by
    have ht := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add (F-P) E)
      (pow_nonneg (norm_nonneg z) 6)
    rw [mul_add] at ht
    dsimp only [D']
    linarith
  have hs := norm_square_energy_error_of_phase_error z F a b D' hz1
    (by dsimp [D']; positivity) herror
  have hcA : (2*I*a)/z^2 = -A/(2*z^2) := by
    dsimp [a]
    field_simp
    ring_nf
    simp [I_sq]
  have hcB : (2*I*b)/z^4 = -B/(8*z^4) := by
    dsimp [b]
    field_simp
    ring_nf
    simp [I_sq]
  rw [hcA,hcB,neg_div,← sub_eq_add_neg,neg_div,← sub_eq_add_neg] at hs
  dsimp only
  rw [← hnorm]
  exact hs.trans (by dsimp [C]; linarith)


end NLS.KdV
