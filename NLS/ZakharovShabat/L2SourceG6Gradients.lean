import NLS.ZakharovShabat.L2GradientFourierRealization

/-! # G.6 majorants for the actual physical L2 gradient coefficients

The previously proved source-norm estimates now control coefficient
vectors explicitly realizing the actual L2 derivatives. The output norm,
H1 source ball, signed indices, spectral hypotheses, and corrected free
reference are unchanged. The outer exponent remains finite.
-/
noncomputable section
open scoped ENNReal
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- One summable majorant controls the actual discriminant-gradient vectors on the exact source ball. -/
theorem sourceG6_l2DiscriminantGradient_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ∃ c : CoeffPair q,
          L2GradientFourierRealizes
            (l2DiscriminantGradient
              (continuousPotentialL2Class (classicalSobolevPotential (sourceG3ClassicalCoefficients a))) (ν n)) c ∧
          ‖c‖ ≤ b n := by
  obtain ⟨b,hb,hb0,h⟩ := sourceG6_discriminant_sourceNorm_majorant p hp q hqfin hq M B hB N₀ ν hν
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  refine ⟨b,hb,hb0,?_⟩
  intro a ha n
  exact ⟨sourceG6DiscriminantCoefficients hq1 _ _,
    sourceG6DiscriminantCoefficients_realizes_l2 hq1 _ _,h a ha n⟩

/-- The actual anti-discriminant error uses the actual free gradient at the signed lattice frequency. -/
theorem sourceG6_l2AntiDiscriminantGradient_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ)) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧ (∀ n, 0 ≤ b n) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M → ∀ n : ℤ,
        ∃ c : CoeffPair q,
          L2GradientFourierRealizes
            (l2AntiDiscriminantGradientRemainder
              (continuousPotentialL2Class (classicalSobolevPotential (sourceG3ClassicalCoefficients a)))
              (ν n) ((Real.pi : ℂ)*n)) c ∧
          ‖c‖ ≤ b n := by
  obtain ⟨b,hb,hb0,h⟩ := sourceG6_antiDiscriminant_sourceNorm_majorant p hp q hqfin hq M B hB N₀ ν hν
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  refine ⟨b,hb,hb0,?_⟩
  intro a ha n
  exact ⟨sourceG6AntiDiscriminantCoefficients hq1 _ _ _,
    sourceG6AntiDiscriminantCoefficients_realizes_l2 hq1 _ _ _,h a ha n⟩

/-- The realized physical coefficient sequence includes every spectral index and belongs to outer lp. -/
theorem sourceG6_l2DiscriminantGradient_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    ∃ c : ℤ → CoeffPair q, Memℓp c (ENNReal.ofReal p) ∧ ∀ n,
      L2GradientFourierRealizes
        (l2DiscriminantGradient
          (continuousPotentialL2Class (classicalSobolevPotential (sourceG3ClassicalCoefficients a)))
          (ν n)) (c n) := by
  obtain ⟨b,hb,_,H⟩ := sourceG6_l2DiscriminantGradient_majorant p hp q hqfin hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  choose c hc hn using H a le_rfl
  exact ⟨c,hb.mono hn,hc⟩

/-- The realized physical coefficient sequence includes every spectral index and belongs to outer lp. -/
theorem sourceG6_l2AntiDiscriminantGradient_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hqfin : q ≠ ⊤)
    (hq : ENNReal.ofReal (1+1/p) < q) (B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) (ν : ℤ → ℂ)
    (hν : ∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (a : ScalarDomain 2 × ScalarDomain 2) :
    ∃ c : ℤ → CoeffPair q, Memℓp c (ENNReal.ofReal p) ∧ ∀ n,
      L2GradientFourierRealizes
        (l2AntiDiscriminantGradientRemainder
          (continuousPotentialL2Class (classicalSobolevPotential (sourceG3ClassicalCoefficients a)))
          (ν n) ((Real.pi : ℂ)*n)) (c n) := by
  obtain ⟨b,hb,_,H⟩ := sourceG6_l2AntiDiscriminantGradient_majorant p hp q hqfin hq
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ B hB N₀ ν hν
  choose c hc hn using H a le_rfl
  exact ⟨c,hb.mono hn,hc⟩

end NLS.ZakharovShabat
