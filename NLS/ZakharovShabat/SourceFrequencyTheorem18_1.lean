import NLS.ZakharovShabat.SourceFrequencyActionExtensions
import NLS.ZakharovShabat.SourceFrequencyActionSpaceAsymptotic

/-! # Theorem 18.1: compatible extensions and locally uniform remainders

One fixed Hilbert action frequency admits analytic extensions at all finite
source exponents above two. Each extension has a locally uniform mixed
l(p/3) + l(1+) remainder, with the neighborhood and both components chosen
before every l(1+) projection exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The analytic extension and mixed asymptotic assertions of Theorem 18.1.
The maps are complex-valued and also analytic over the real scalars. -/
theorem exists_sourceFrequency_theorem18_1 :
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
          ∀ b ∈ V₁, ∀ n, F b n = ωstar b n) ∧
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
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,ωstar,hV₁,hpos,hreal,hfamily,_⟩ :=
    exists_sourceFrequency_actionExtensions
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,ωstar,hV₁,hpos,hreal,hfamily,?_⟩
  intro p q instP instQ instHolder hp hp2
  have hp1 : 1 < p := lt_trans (by norm_num) hp2
  have hq : q ≠ ⊤ := Coeff.doublingExponent_ne_top hp
  have hq1 : 1 < q := by
    apply (ENNReal.toReal_lt_toReal (by simp) hq).mp
    have hpr := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp2
    norm_num at hpr ⊢
    linarith [Coeff.doublingExponent_toReal (p := p) (q := q)]
  have hhalf : ENNReal.ofReal (p.toReal/2) = q := by
    calc
      ENNReal.ofReal (p.toReal/2) = ENNReal.ofReal q.toReal := by
        congr 1
        rw [Coeff.doublingExponent_toReal (p := p) (q := q)]
        ring
      _ = q := ENNReal.ofReal_toReal hq
  obtain ⟨Wp,sp,Ap,Pp,hsp,Wp₀,Bp,Xp,tp,Dp,V,hV,_,hposp,⟨Y,hY,hrealY,hYX,himage⟩,hfreq⟩ :=
    exists_sourceFrequency_actionSpace_asymptotic (q := q) hp hp1 hp2.le
  obtain ⟨F,hF,hFR,hrec,hcorr,hlocal⟩ := hfreq q hq hq1 (by rw [hhalf])
  refine ⟨V,hV,hposp,⟨tp,Y,hY,hrealY,?_⟩,F,hF,hFR,?_,hcorr,?_⟩
  · intro hp' hp1'
    exact ⟨himage,fun ψ hψ n => Dp.actionSequence_apply ψ (hYX hψ) n⟩
  · intro b hb n
    have he : Coeff.exponentInclusion (le_refl (1 : ℝ≥0∞)) (RealCoeff.complexCLM 1 b) =
        RealCoeff.complexCLM 1 b := by ext k; rfl
    have h := Ap.actionMap_eq_on_nonnegative_summable A hsp hs Dp D hp2.le le_rfl
      (fun c k => F c k) ωstar (fun ψ => (hrec ψ).2) (fun ψ => (hreal ψ).2) b hb n
    simpa only [he] using h
  · intro b hb
    obtain ⟨T,hT,hbT,hTV,_,hmixed⟩ := hlocal b hb
    exact ⟨T,hT,hbT,hTV,hmixed⟩

end NLS.ZakharovShabat
