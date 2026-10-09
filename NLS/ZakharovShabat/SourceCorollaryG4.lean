import NLS.ZakharovShabat.SourceLemmaG3
import NLS.ZakharovShabat.ClassicalFourierSequenceSummability

/-! # Corollary G.4 for full matrices on the original H¹ source

For every finite p > 1 and every q > 1+1/p, including q = infinity,
the actual full-matrix Fourier norms have a common nonnegative ℓp majorant
on each exact Chapter 5 source-norm ball. The tail majorant is uniform over
spectral sequences with one common displacement bound; the whole-sequence
majorant may depend on their unrestricted finite initial values.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Common summable tails for full remainders, uniform over both source balls and spectral tails. -/
theorem sourceG4_remainder_tail_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ (N : ℕ) (b : ℤ → ℝ), 0 < N ∧ Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ (ν : ℤ → ℂ),
        (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianRemainderFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (sourceG3ClassicalCoefficients a) (ν n)‖ ≤ b n := by
  obtain ⟨N,b,hN,hb,h⟩ := exists_classicalSobolevRemainder_fourier_memlp_majorant p hp q hq (2*M) B hB N₀
  refine ⟨N,(fun n => 4*‖b n‖),hN,hb.norm.const_mul 4,fun n => by positivity,?_⟩
  intro ν hν a ha n hn
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*M :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)
  apply (norm_hermitianObservationAssembly_le _ (b n) (fun v L hL => h ν hν _ ha' v L hL n hn)).trans
  exact mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num)

/-- Common summable tails for M(nu_n)-E_(n*pi) under inverse-index displacement. -/
theorem sourceG4_shiftedFree_tail_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ (N : ℕ) (b : ℤ → ℝ), 0 < N ∧ Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ (ν : ℤ → ℂ),
        (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianShiftedFreeFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ))‖ ≤ b n := by
  obtain ⟨N,b,hN,hb,h⟩ := exists_classicalShiftedFree_fourier_memlp_majorant p hp q hq (2*M) B hB N₀
  refine ⟨N,(fun n => 4*‖b n‖),hN,hb.norm.const_mul 4,fun n => by positivity,?_⟩
  intro ν hν a ha n hn
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*M :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)
  apply (norm_hermitianObservationAssembly_le _ (b n) (fun v L hL => h ν hν _ ha' v L hL n hn)).trans
  exact mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num)

/-- A whole-sequence majorant uniform on each exact source-norm ball.
The finite initial spectral values are arbitrary and may enter the majorant. -/
theorem sourceG4_remainder_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
      ‖classicalHermitianRemainderFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (sourceG3ClassicalCoefficients a) (ν n)‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalSobolevRemainder_fourier_uniform_memlp p hp q hq (2*M) B hB N₀ ν hν
  refine ⟨(fun n => 4*‖b n‖),hb.norm.const_mul 4,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*M :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)
  apply (norm_hermitianObservationAssembly_le _ (b n) (fun v L hL => h _ ha' v L hL n)).trans
  exact mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num)

/-- A whole-sequence majorant for the full shifted-free matrix, uniform on source balls. -/
theorem sourceG4_shiftedFree_uniform_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
      ‖classicalHermitianShiftedFreeFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ))‖ ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalShiftedFree_fourier_uniform_memlp p hp q hq (2*M) B hB N₀ ν hν
  refine ⟨(fun n => 4*‖b n‖),hb.norm.const_mul 4,fun n => by positivity,?_⟩
  intro a ha n
  have ha' : ‖sourceG3ClassicalCoefficients a‖ ≤ 2*M :=
    (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)
  apply (norm_hermitianObservationAssembly_le _ (b n) (fun v L hL => h _ ha' v L hL n)).trans
  exact mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num)

/-- The first assertion of printed G.4, with its literal eventual pi/4 hypothesis. -/
theorem sourceCorollaryG4
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (M : ℝ) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ Real.pi/4) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
      ‖classicalHermitianRemainderFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (sourceG3ClassicalCoefficients a) (ν n)‖ ≤ b n :=
  sourceG4_remainder_uniform_majorant p hp q hq M (Real.pi/4) (by positivity) N₀ ν hν

/-- Actual full-matrix Fourier norms form an ℓp sequence, with arbitrary finite initial values. -/
theorem sourceG4_remainder_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianRemainderFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (sourceG3ClassicalCoefficients a) (ν n)‖) (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG4_remainder_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl n

/-- The shifted-free assertion of G.4 for the actual full-matrix Fourier norms. -/
theorem sourceG4_shiftedFree_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => ‖classicalHermitianShiftedFreeFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ))‖)
      (ENNReal.ofReal p) := by
  obtain ⟨b,hb,_,h⟩ := sourceG4_shiftedFree_uniform_majorant p hp q hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  apply hb.mono
  intro n
  simpa only [norm_norm] using h a le_rfl n

/-- The actual operator-valued Fourier sequences themselves form an ℓp sequence. -/
theorem sourceG4_remainder_operator_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianRemainderFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (sourceG3ClassicalCoefficients a) (ν n)) (ENNReal.ofReal p) :=
  (sourceG4_remainder_memlp p hp q hq B hB N₀ ν hν a).of_norm

/-- The full shifted-free operator-valued Fourier sequences are also in ℓp. -/
theorem sourceG4_shiftedFree_operator_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    Memℓp (fun n : ℤ => classicalHermitianShiftedFreeFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ)))
      (ENNReal.ofReal p) :=
  (sourceG4_shiftedFree_memlp p hp q hq B hB N₀ ν hν a).of_norm

end NLS.ZakharovShabat
