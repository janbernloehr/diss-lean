import NLS.KdV.FrequencyMoments

/-! # The finite-gap contour algebra of the KdV/KdV2 frequencies

This is the contour part of Lemmas 3.2 and 4.1 of arXiv:1605.06690v1.
The cubic and fifth-power outer periods are deformed by the existing
finite-hole Cauchy theorem; odd moments vanish by analytic continuation.
All normalized coefficients and leading powers are then proved exactly.
The identification of those outer periods with Hamiltonian frequencies
still requires the physical spectral and Poisson constructions.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem cubic_frequency_gap_contribution (F G : ℂ → ℂ) (c : ℂ) (r k : ℝ) (hr : 0 ≤ r)
    (hF : ContinuousOn F (sphere c r)) (hG : ContinuousOn G (sphere c r))
    (hF2 : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) :
    (4 / (I * Real.pi) : ℂ) * (∮ z in C(c,r), (F z - I * k * Real.pi) ^ 3 * G z) =
      -12 * (k : ℂ) * frequencyMoment F G c r 2 +
        4 * (k : ℂ) ^ 3 * (Real.pi : ℂ) ^ 2 * frequencyMoment F G c r 0 := by
  rw [cubic_shift_frequency_period F G c (I * k * Real.pi) r hr hF hG hF2 hFG]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

theorem fifth_frequency_gap_contribution (F G : ℂ → ℂ) (c : ℂ) (r k : ℝ) (hr : 0 ≤ r)
    (hF : ContinuousOn F (sphere c r)) (hG : ContinuousOn G (sphere c r))
    (hF2 : AnalyticOnNhd ℂ (fun z => F z ^ 2) (closedBall c r))
    (hFG : AnalyticOnNhd ℂ (fun z => F z * G z) (closedBall c r)) :
    (-16 / (I * Real.pi) : ℂ) * (∮ z in C(c,r), (F z - I * k * Real.pi) ^ 5 * G z) =
      80 * (k : ℂ) * frequencyMoment F G c r 4 -
        160 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 3 * frequencyMoment F G c r 2 +
          16 * (Real.pi : ℂ) ^ 4 * (k : ℂ) ^ 5 * frequencyMoment F G c r 0 := by
  rw [fifth_shift_frequency_period F G c (I * k * Real.pi) r hr hF hG hF2 hFG]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring_nf
  simp only [I_pow_four, mul_one]

/-- The cubic outer period, minus its leading linear frequency, is the
finite sum -12 sum k*Omega^(2). The selected mode n is included among the
isolating circles, even when its physical gap is collapsed. -/
theorem kdv_frequency_contour_decomposition
    (d : ℂ) (S : ℝ) (hS : 0 ≤ S) (A : Finset ℕ+) (n : ℕ+) (hn : n ∈ A)
    (c : ℕ+ → ℂ) (r R : ℕ+ → ℝ) (Q : ℂ → ℂ) (F G : ℕ+ → ℂ → ℂ)
    (hr : ∀ k ∈ A, 0 < r k) (hrR : ∀ k ∈ A, r k < R k)
    (henclosed : ∀ k ∈ A, closedBall (c k) (R k) ⊆ ball d S)
    (hdisj : ∀ k ∈ A, ∀ j ∈ A, k ≠ j →
      Disjoint (closedBall (c k) (R k)) (closedBall (c j) (R j)))
    (hQ : AnalyticOnNhd ℂ Q (ComplexAnalysis.circleHoleDomain d S A c r))
    (hF : ∀ k ∈ A, ContinuousOn (F k) (sphere (c k) (r k)))
    (hG : ∀ k ∈ A, ContinuousOn (G k) (sphere (c k) (r k)))
    (hF2 : ∀ k ∈ A, AnalyticOnNhd ℂ (fun z => F k z ^ 2) (closedBall (c k) (r k)))
    (hFG : ∀ k ∈ A, AnalyticOnNhd ℂ (fun z => F k z * G k z) (closedBall (c k) (r k)))
    (hzero : ∀ k ∈ A, frequencyMoment (F k) (G k) (c k) (r k) 0 =
      (2 * Real.pi : ℂ) * if k = n then 1 else 0)
    (hmatch : ∀ k ∈ A, ∀ z ∈ sphere (c k) (r k),
      Q z = (F k z - I * (k : ℂ) * Real.pi) ^ 3 * G k z) :
    (4 / (I * Real.pi) : ℂ) * (∮ z in C(d,S), Q z) - (2 * (n : ℂ) * Real.pi) ^ 3 =
      -12 * ∑ k ∈ A, (k : ℂ) * frequencyMoment (F k) (G k) (c k) (r k) 2 := by
  have hlocal (k : ℕ+) (hk : k ∈ A) :
      (4 / (I * Real.pi) : ℂ) * (∮ z in C(c k,r k), Q z) =
        -12 * (k : ℂ) * frequencyMoment (F k) (G k) (c k) (r k) 2 +
          if k = n then (2 * (n : ℂ) * Real.pi) ^ 3 else 0 := by
    rw [circleIntegral.integral_congr (hr k hk).le (hmatch k hk)]
    have h := cubic_frequency_gap_contribution (F k) (G k) (c k) (r k) (k : ℝ)
      (hr k hk).le (hF k hk) (hG k hk) (hF2 k hk) (hFG k hk)
    have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_cast
    rw [hcast] at h
    rw [h, hzero k hk]
    split_ifs with he
    · subst k
      ring
    · ring
  rw [ComplexAnalysis.circleIntegral_eq_sum_of_finite_holes d S hS A c r R Q
    hr hrR henclosed hdisj hQ, Finset.mul_sum]
  simp_rw [Finset.sum_congr rfl (fun k hk => hlocal k hk)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', hn, if_true]
  rw [Finset.mul_sum]
  ring

/-- The fifth outer period corresponds to the mass-renormalized Hamiltonian
H2-10H0^2. Its leading-power subtraction gives exactly the two moment sums
in source formula (84); no physical frequency identity is assumed here. -/
theorem kdv2_frequency_contour_decomposition
    (d : ℂ) (S : ℝ) (hS : 0 ≤ S) (A : Finset ℕ+) (n : ℕ+) (hn : n ∈ A)
    (c : ℕ+ → ℂ) (r R : ℕ+ → ℝ) (Q : ℂ → ℂ) (F G : ℕ+ → ℂ → ℂ)
    (hr : ∀ k ∈ A, 0 < r k) (hrR : ∀ k ∈ A, r k < R k)
    (henclosed : ∀ k ∈ A, closedBall (c k) (R k) ⊆ ball d S)
    (hdisj : ∀ k ∈ A, ∀ j ∈ A, k ≠ j →
      Disjoint (closedBall (c k) (R k)) (closedBall (c j) (R j)))
    (hQ : AnalyticOnNhd ℂ Q (ComplexAnalysis.circleHoleDomain d S A c r))
    (hF : ∀ k ∈ A, ContinuousOn (F k) (sphere (c k) (r k)))
    (hG : ∀ k ∈ A, ContinuousOn (G k) (sphere (c k) (r k)))
    (hF2 : ∀ k ∈ A, AnalyticOnNhd ℂ (fun z => F k z ^ 2) (closedBall (c k) (r k)))
    (hFG : ∀ k ∈ A, AnalyticOnNhd ℂ (fun z => F k z * G k z) (closedBall (c k) (r k)))
    (hzero : ∀ k ∈ A, frequencyMoment (F k) (G k) (c k) (r k) 0 =
      (2 * Real.pi : ℂ) * if k = n then 1 else 0)
    (hmatch : ∀ k ∈ A, ∀ z ∈ sphere (c k) (r k),
      Q z = (F k z - I * (k : ℂ) * Real.pi) ^ 5 * G k z) :
    (-16 / (I * Real.pi) : ℂ) * (∮ z in C(d,S), Q z) - (2 * (n : ℂ) * Real.pi) ^ 5 =
      -160 * (Real.pi : ℂ) ^ 2 * (∑ k ∈ A, (k : ℂ) ^ 3 * frequencyMoment (F k) (G k) (c k) (r k) 2) +
        80 * ∑ k ∈ A, (k : ℂ) * frequencyMoment (F k) (G k) (c k) (r k) 4 := by
  have hlocal (k : ℕ+) (hk : k ∈ A) :
      (-16 / (I * Real.pi) : ℂ) * (∮ z in C(c k,r k), Q z) =
        80 * (k : ℂ) * frequencyMoment (F k) (G k) (c k) (r k) 4 -
          160 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 3 * frequencyMoment (F k) (G k) (c k) (r k) 2 +
            if k = n then (2 * (n : ℂ) * Real.pi) ^ 5 else 0 := by
    rw [circleIntegral.integral_congr (hr k hk).le (hmatch k hk)]
    have h := fifth_frequency_gap_contribution (F k) (G k) (c k) (r k) (k : ℝ)
      (hr k hk).le (hF k hk) (hG k hk) (hF2 k hk) (hFG k hk)
    have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_cast
    rw [hcast] at h
    rw [h, hzero k hk]
    split_ifs with he
    · subst k
      ring
    · ring
  rw [ComplexAnalysis.circleIntegral_eq_sum_of_finite_holes d S hS A c r R Q
    hr hrR henclosed hdisj hQ, Finset.mul_sum]
  simp_rw [Finset.sum_congr rfl (fun k hk => hlocal k hk)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', hn, if_true]
  simp only [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, mul_assoc]
  ring

end NLS.KdV
