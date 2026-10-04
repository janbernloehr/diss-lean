import NLS.ZakharovShabat.SourceActionFrequencyCorrection

/-! # Equation (4.12) on the source neighborhood

The correction omega*_n + 2 I_n is analytic in each refined sequence
space. One fixed lp/3 + l(1+) decomposition has locally uniform bounds.
This proves the source-space asymptotic used in Theorem 18.1; the
factorization through action variables remains a separate step.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the actual action-frequency correction and its refined
analyticity, physical finite-gap identity, and fixed mixed remainder. -/
theorem exists_sourceActionFrequency_asymptotic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
          ENNReal.ofReal (p.toReal/3) ≤ r →
          (∀ ψ ∈ U, ∀ n, A.actionFrequencyCorrectionSequence r ψ n =
            A.renormalizedFrequency n ψ + 2*sourceComplexAction hp hp1 n ψ) ∧
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r) U ∧
          AnalyticOnNhd ℝ (A.actionFrequencyCorrectionSequence r) U) ∧
        (∀ (W₀ B X : Set (CoeffPair 2)) (t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
          (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
          (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ),
          A.actionFrequencyCorrection φ.val n =
            D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
              4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2 +
                2*sourceComplexAction hp hp1 n φ.val) ∧
        ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
          (∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
              (∀ n, b n = A.actionFrequencyCorrection ψ n) ∧ ‖b‖ ≤ C) ∧
          ∃ a : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/3)),
          ∃ b : CoeffPair p → CoeffOnePlus,
            (∀ ψ ∈ T, ∀ n, A.renormalizedFrequency n ψ +
              2*sourceComplexAction hp hp1 n ψ = a ψ n + (b ψ).1 n) ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖a ψ‖ ≤ C) ∧
            ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
              ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b ψ)‖ ≤ C := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,hUc,hreal,hUV,ha,hlocal⟩ := A.exists_actionFrequencyCorrection_neighborhood hs hV hrealV
  refine ⟨W,s,A,U,hU,hUc,hreal,fun ψ hψ => (hUV hψ).1,?_,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,hanalytic⟩ := Coeff.analytic_realization_of_local_bounds
      A.actionFrequencyCorrection hU ha (by
        intro φ hφ
        obtain ⟨T,hT,hφT,hTU,hb⟩ := hlocal φ hφ
        obtain ⟨C,_,hb⟩ := hb r hr hr1 hpr
        exact ⟨T,hT,hφT,hTU,C,hb⟩)
    exact ⟨he,hanalytic,hanalytic.restrictScalars⟩
  · intro W₀ B X t D φ hf n
    unfold SourceAbelianMomentAtlas.actionFrequencyCorrection
    rw [A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D
      hs.toSourcePsiIsolatingComplexExtension φ hf n]
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,hb⟩ := hlocal φ hφ
    exact ⟨T,hT,hφT,hTU,hb,Coeff.exists_onePlus_decomposition_of_refined T
      A.actionFrequencyCorrection ENNReal.ofReal_ne_top hb⟩

end NLS.ZakharovShabat
