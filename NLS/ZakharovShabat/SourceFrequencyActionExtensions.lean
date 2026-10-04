import NLS.ZakharovShabat.SourceFrequencyActionExponentCompatibility
import NLS.SequenceSpaces.ActionCorrectionIdentity

/-! # One frequency map and its compatible action-space extensions

Fix the Hilbert action-frequency map once. It has analytic realizations
in every finite lr above one on a common l1 action neighborhood. At each
larger source exponent, an analytic half-exponent action map extends those
same values on the full nonnegative summable cone, with analytic refined
corrections on a common domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The analytic extension part of Theorem 18.1, with one fixed actual
Hilbert frequency, all finite targets above one, and compatible extensions
at every finite source exponent above two. Local uniform mixed bounds are
not included in this statement. -/
theorem exists_sourceFrequency_actionExtensions :
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
            ∀ (u : ℝ≥0∞) [Fact (1 ≤ u)], u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
              ∃ H : Coeff q → Coeff u, AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℝ H V ∧
                ∀ b ∈ V, ∀ n, H b n = F b n+2*b n := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,hV₁,hcenters,hpos,_,_,huniq,hfreq,_⟩ :=
    exists_sourceFrequency_actionSpace_maps (p := 2) (q := 1) (by simp) (by norm_num) le_rfl
  obtain ⟨F₀,hF₀,hrec₀⟩ := hfreq 2 (by simp) (by norm_num) (by norm_num)
  let ωstar : Coeff 1 → ℤ → ℂ := fun b n => F₀ b n
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V₁,ωstar,hV₁,?_,
    fun ψ => ⟨hcenters ψ,(hrec₀ ψ).2⟩,?_,?_⟩
  · intro b hb
    have he : Coeff.exponentInclusion (le_refl (1 : ℝ≥0∞)) (RealCoeff.complexCLM 1 b) =
        RealCoeff.complexCLM 1 b := by ext n; rfl
    simpa only [he] using hpos b hb
  · intro r inst hr hr1
    obtain ⟨F,hF,hrec⟩ := hfreq r hr hr1 (by simpa using hr1.le)
    refine ⟨F,hF,hF.restrictScalars,?_⟩
    intro b hb n
    apply huniq (fun c => F c n) (fun c => F₀ c n)
      (fun c hc => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n).analyticAt _).comp (hF c hc))
      (fun c hc => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (hF₀ c hc))
      (fun ψ => ((hrec ψ).2 n).trans ((hrec₀ ψ).2 n).symm) hb
  · intro p q instP instQ instHolder hp hp2
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
    obtain ⟨Wp,sp,Ap,Pp,hsp,Wp₀,Bp,Xp,tp,Dp,V,hV,_,hposp,_,⟨Y,hY,hrealY,hYX,himage⟩,huniqp,hfreqp,hcorrp⟩ :=
      exists_sourceFrequency_actionSpace_maps (q := q) hp hp1 hp2.le
    obtain ⟨F,hF,hrec⟩ := hfreqp q hq hq1 (by rw [hhalf])
    refine ⟨V,hV,hposp,⟨tp,Y,hY,hrealY,?_⟩,F,hF,hF.restrictScalars,?_,?_⟩
    · intro hp' hp1'
      exact ⟨himage,fun ψ hψ n => Dp.actionSequence_apply ψ (hYX hψ) n⟩
    · intro b hb n
      have he : Coeff.exponentInclusion (le_refl (1 : ℝ≥0∞)) (RealCoeff.complexCLM 1 b) =
          RealCoeff.complexCLM 1 b := by ext k; rfl
      have h := Ap.actionMap_eq_on_nonnegative_summable A hsp hs Dp D hp2.le le_rfl
        (fun c k => F c k) (fun c k => F₀ c k) (fun ψ => (hrec ψ).2) (fun ψ => (hrec₀ ψ).2) b hb n
      simpa only [he] using h
    · intro u instU hu hu1 hpu
      obtain ⟨H,hH,hrecH⟩ := hcorrp u hu hu1 hpu
      refine ⟨H,hH,hH.restrictScalars,?_⟩
      apply Coeff.actionCorrection_eq_of_analytic_uniqueness
        (fun ψ : realTypeSourceSubmodule p => sourceActionSequence hp hp1 tp ψ.val) V huniqp F H hF hH
      intro ψ n
      rw [(hrecH ψ).2 n,(hrec ψ).2 n]

end NLS.ZakharovShabat
