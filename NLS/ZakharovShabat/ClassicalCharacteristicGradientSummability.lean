import NLS.ZakharovShabat.ClassicalCharacteristicGradientFourier
import NLS.ZakharovShabat.ClassicalEndpointGradientFiniteSummability

/-! # G.6: summable discriminant and anti-discriminant gradients

Each characteristic uses two of the already controlled endpoint gradients.
The actual Fourier norms have a common summable majorant over every H¹
ball and all contractive scalar observations. Finite heads are unrestricted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- G.6's discriminant gradient has a common outer ℓp majorant on each physical H¹ ball. -/
theorem exists_classicalDiscriminantGradient_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalDiscriminantGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) P‖ ≤ b n := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_fourier_uniform_memlp p hp q hq M hM B hB N₀ ν hν
  refine ⟨fun n => b n+b n,hb.add hb,?_⟩
  intro a ha P hP n
  exact (norm_add_le _ _).trans (add_le_add
    (h a ha (1,0) (by simp) _ (ContinuousLinearMap.norm_fst_le ..) P hP n)
    (h a ha (0,1) (by simp) _ (ContinuousLinearMap.norm_snd_le ..) P hP n))

/-- Actual Fourier norms satisfy G.6 at every target exponent above the finite-p threshold. -/
theorem memlp_classicalDiscriminantGradient_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalDiscriminantGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a) (ν n) P‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalDiscriminantGradient_fourier_uniform_memlp p hp q hq
    ‖a‖ (norm_nonneg a) B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl P hP n

/-- The printed conjugate Fourier exponent p′ is covered for every finite p>1. -/
theorem memlp_classicalDiscriminantGradient_conjugate_fourier_norms
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
      (classicalSobolevPotential a) (ν n) P‖) (ENNReal.ofReal p) :=
  memlp_classicalDiscriminantGradient_fourier_norms p hp _ (conjugate_exponent_ennreal_gt_gradient_threshold p hp)
    B hB N₀ ν hν a P hP

/-- G.6's anti-discriminant error has a common outer ℓp majorant on each physical H¹ ball. -/
theorem exists_classicalAntiDiscriminantGradient_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalAntiDiscriminantGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) P‖ ≤ b n := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_shifted_fourier_uniform_memlp p hp q hq M hM B hB N₀ ν hν
  refine ⟨fun n => b n+b n,hb.add hb,?_⟩
  intro a ha P hP n
  exact (norm_add_le _ _).trans (add_le_add
    (h a ha (0,1) (by simp) _ (ContinuousLinearMap.norm_fst_le ..) P hP n)
    (h a ha (1,0) (by simp) _ (ContinuousLinearMap.norm_snd_le ..) P hP n))

/-- Actual Fourier norms satisfy G.6 at every target exponent above the finite-p threshold. -/
theorem memlp_classicalAntiDiscriminantGradient_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalAntiDiscriminantGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) P‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalAntiDiscriminantGradient_fourier_uniform_memlp p hp q hq
    ‖a‖ (norm_nonneg a) B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl P hP n

/-- The printed conjugate Fourier exponent p′ is covered for every finite p>1. -/
theorem memlp_classicalAntiDiscriminantGradient_conjugate_fourier_norms
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalAntiDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
      (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) P‖) (ENNReal.ofReal p) :=
  memlp_classicalAntiDiscriminantGradient_fourier_norms p hp _ (conjugate_exponent_ennreal_gt_gradient_threshold p hp)
    B hB N₀ ν hν a P hP

/-- Both physical components are summable together, in the stronger component-sum norm. -/
theorem memlp_classicalDiscriminantGradient_conjugate_component_sum
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ =>
      ‖classicalDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
        (classicalSobolevPotential a) (ν n) (ContinuousLinearMap.fst ℝ ℂ ℂ)‖+
      ‖classicalDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
        (classicalSobolevPotential a) (ν n) (ContinuousLinearMap.snd ℝ ℂ ℂ)‖)
      (ENNReal.ofReal p) :=
  (memlp_classicalDiscriminantGradient_conjugate_fourier_norms p hp B hB N₀ ν hν a
    _ (ContinuousLinearMap.norm_fst_le ..)).add
    (memlp_classicalDiscriminantGradient_conjugate_fourier_norms p hp B hB N₀ ν hν a
      _ (ContinuousLinearMap.norm_snd_le ..))

/-- Both physical components are summable together, in the stronger component-sum norm. -/
theorem memlp_classicalAntiDiscriminantGradient_conjugate_component_sum
    (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ =>
      ‖classicalAntiDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
        (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) (ContinuousLinearMap.fst ℝ ℂ ℂ)‖+
      ‖classicalAntiDiscriminantGradientFourierCoefficients (q := ENNReal.ofReal (p/(p-1)))
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp))
        (classicalSobolevPotential a) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) (ContinuousLinearMap.snd ℝ ℂ ℂ)‖)
      (ENNReal.ofReal p) :=
  (memlp_classicalAntiDiscriminantGradient_conjugate_fourier_norms p hp B hB N₀ ν hν a
    _ (ContinuousLinearMap.norm_fst_le ..)).add
    (memlp_classicalAntiDiscriminantGradient_conjugate_fourier_norms p hp B hB N₀ ν hν a
      _ (ContinuousLinearMap.norm_snd_le ..))

end NLS.ZakharovShabat
