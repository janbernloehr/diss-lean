import NLS.ZakharovShabat.SourceFrequencyTheorem18_1
import NLS.ZakharovShabat.SourceFrequencyReality

/-! # Theorem 18.1 with its real sequence-space range

The fixed actual frequency on nonnegative summable actions has real-valued
analytic extensions in every finite target exponent above one. All complex
extensions and locally uniform mixed remainders are retained.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The real range assertion completes the sequence-space statement of
Theorem 18.1, alongside its compatible complex extensions and remainders. -/
theorem exists_sourceFrequency_theorem18_1_real :
    ∃ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
    ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s,
    ∃ P : Set (CoeffPair 2), SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s ∧
    ∃ W₀ B X : Set (CoeffPair 2), ∃ t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
    ∃ _D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
    ∃ V₁ : Set (Coeff 1), ∃ ωstar : Coeff 1 → ℤ → ℂ,
      IsOpen V₁ ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → RealCoeff.complexCLM 1 b ∈ V₁) ∧
      (∀ ψ : realTypeSourceSubmodule 2,
        sourceActionSequence (q := 1) (by simp) (by norm_num) t ψ.val ∈ V₁ ∧
        ∀ n, ωstar (sourceActionSequence (q := 1) (by simp) (by norm_num) t ψ.val) n =
          A.renormalizedFrequency n ψ.val) ∧
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
        ∃ F : Coeff 1 → Coeff r, AnalyticOnNhd ℂ F V₁ ∧ AnalyticOnNhd ℝ F V₁ ∧
          (∀ b ∈ V₁, ∀ n, F b n = ωstar b n) ∧
          ∃ R : RealCoeff 1 → RealCoeff r,
            AnalyticOnNhd ℝ R (RealCoeff.complexCLM 1 ⁻¹' V₁) ∧
            ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n, (R b n : ℂ) = ωstar (RealCoeff.complexCLM 1 b) n) ∧
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q],
        p ≠ ⊤ → 2 < p →
        ∃ V : Set (Coeff q), IsOpen V ∧
          (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
            Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
          (∃ t' : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
            ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧
              ∀ (hp : p ≠ ⊤) (hp1 : 1 < p),
                sourceActionSequence (q := q) hp hp1 t' '' Y = V ∧
                ∀ ψ ∈ Y, ∀ n, sourceActionSequence (q := q) hp hp1 t' ψ n =
                  sourceComplexAction hp hp1 n ψ) ∧
          ∃ F : Coeff q → Coeff q, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧
            (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n,
              F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) n =
                ωstar (RealCoeff.complexCLM 1 b) n) ∧
            (∀ (u : ℝ≥0∞) [Fact (1 ≤ u)], u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
              ∃ H : Coeff q → Coeff u, AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℝ H V ∧
                ∀ b ∈ V, ∀ n, H b n = F b n+2*b n) ∧
            ∀ b ∈ V, ∃ T : Set (Coeff q), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
              ∃ g : Coeff q → Coeff (ENNReal.ofReal (p.toReal/3)), ∃ h : Coeff q → CoeffOnePlus,
                (∀ c ∈ T, ∀ n, F c n+2*c n = g c n+(h c).1 n) ∧
                (∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖g c‖ ≤ M) ∧
                ∀ (u : ℝ≥0∞) (hu1 : 1 < u) (hu : u ≠ ⊤),
                  ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖CoeffOnePlus.toCoeff u hu1 hu (h c)‖ ≤ M := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,ωstar,hV₁,hpos,hreal,hfamily,higher⟩ :=
    exists_sourceFrequency_theorem18_1
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,ωstar,hV₁,hpos,hreal,?_,higher⟩
  intro r inst hr hr1
  obtain ⟨F,hF,hFR,he⟩ := hfamily r hr hr1
  have hrec : ∀ ψ : realTypeSourceSubmodule 2, ∀ n,
      F (sourceActionSequence (q := 1) (by simp) (by norm_num) t ψ.val) n =
        A.renormalizedFrequency n ψ.val := by
    intro ψ n
    exact (he _ (hreal ψ).1 n).trans ((hreal ψ).2 n)
  obtain ⟨U,hU,hUeq,R,hR,hReq⟩ := A.exists_real_analytic_actionMap hs D le_rfl F hV₁ hF hrec
  refine ⟨F,hF,hFR,he,R,?_,?_⟩
  · simpa only [hUeq] using hR
  · intro b hb n
    have hbU : b ∈ U := by rw [hUeq]; exact hpos b hb
    have heq := congrArg (fun c : Coeff r => c n) (hReq b hbU hb)
    exact heq.trans (he _ (hpos b hb) n)

end NLS.ZakharovShabat
