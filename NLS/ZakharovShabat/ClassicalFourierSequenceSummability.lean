import NLS.ZakharovShabat.ClassicalFourierTailSummability
import NLS.ZakharovShabat.ClassicalFourierBoundAllFrequencies

/-! # Corollary G.4 for complete spectral sequences

The finite head has a uniform bound on each Sobolev ball at its fixed
frequencies. Splicing it with the common tail majorant gives one ℓp
majorant for the whole sequence and every potential in the ball.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A whole-sequence ℓp majorant, uniform on the physical H¹ coefficient ball. -/
theorem exists_classicalSobolevRemainder_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalSobolevRemainderFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a (ν n) v L‖ ≤ b n*‖v‖ := by
  obtain ⟨N,b,_hN,hb,h⟩ := exists_classicalSobolevRemainder_fourier_memlp_majorant p hp q hq M B hB N₀
  let K (n : ℤ) := classicalFourierReferenceBound (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) (4*M) (ν n) (ν n)
  let c (n : ℤ) := if N ≤ n.natAbs then ‖b n‖ else ‖K n‖
  refine ⟨c,?_,?_⟩
  · apply memlp_of_natAbs_eventual_bound p (by linarith) c (fun n => ‖b n‖) hb.norm N
    intro n hn
    simp [c,hn]
  intro a ha v L hL n
  by_cases hn : N ≤ n.natAbs
  · exact (h ν hν a ha v L hL n hn).trans (by
      dsimp only [c]
      rw [if_pos hn]
      exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _))
  · have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
      (norm_classicalSobolevPotential_le a).trans (by linarith)
    have hhead := norm_classicalFourierReference_le (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) (4*M)
      (classicalSobolevPotential a) hφ (ν n) (ν n) v L hL
    exact hhead.trans (by
      dsimp only [c]
      rw [if_neg hn]
      exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _))

/-- The actual Fourier norms form an ℓp sequence, with an arbitrary finite spectral head. -/
theorem memlp_classicalSobolevRemainder_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalSobolevRemainderFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a (ν n) v L‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalSobolevRemainder_fourier_uniform_memlp p hp q hq ‖a‖ B hB N₀ ν hν
  apply (hb.const_mul ‖v‖).mono
  intro n
  simpa only [norm_norm,mul_comm] using h a le_rfl v L hL n

/-- A whole-sequence ℓp majorant, uniform on the physical H¹ coefficient ball. -/
theorem exists_classicalShiftedFree_fourier_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalShiftedFreeFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) (Real.pi*(n : ℝ)) v L‖ ≤ b n*‖v‖ := by
  obtain ⟨N,b,_hN,hb,h⟩ := exists_classicalShiftedFree_fourier_memlp_majorant p hp q hq M B hB N₀
  let K (n : ℤ) := classicalFourierReferenceBound (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) (4*M) (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ)
  let c (n : ℤ) := if N ≤ n.natAbs then ‖b n‖ else ‖K n‖
  refine ⟨c,?_,?_⟩
  · apply memlp_of_natAbs_eventual_bound p (by linarith) c (fun n => ‖b n‖) hb.norm N
    intro n hn
    simp [c,hn]
  intro a ha v L hL n
  by_cases hn : N ≤ n.natAbs
  · exact (h ν hν a ha v L hL n hn).trans (by
      dsimp only [c]
      rw [if_pos hn]
      exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _))
  · have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
      (norm_classicalSobolevPotential_le a).trans (by linarith)
    have hhead := norm_classicalFourierReference_le (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) (4*M)
      (classicalSobolevPotential a) hφ (ν n) ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L hL
    exact hhead.trans (by
      dsimp only [c]
      rw [if_neg hn]
      exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _))

/-- The actual Fourier norms form an ℓp sequence, with an arbitrary finite spectral head. -/
theorem memlp_classicalShiftedFree_fourier_norms
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalShiftedFreeFourierCoefficients (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) (Real.pi*(n : ℝ)) v L‖) (ENNReal.ofReal p) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalShiftedFree_fourier_uniform_memlp p hp q hq ‖a‖ B hB N₀ ν hν
  apply (hb.const_mul ‖v‖).mono
  intro n
  simpa only [norm_norm,mul_comm] using h a le_rfl v L hL n

end NLS.ZakharovShabat
