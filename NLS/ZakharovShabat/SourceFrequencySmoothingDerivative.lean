import NLS.ZakharovShabat.SourceFrequencyActionSpaceAsymptotic
import NLS.ZakharovShabat.SourceFrequencyOrigin
import NLS.SequenceSpaces.RefinedActionExponent
import NLS.SequenceSpaces.RefinedActionDerivative

/-! # The refined derivative in Corollary 18.2

The actual action frequency vanishes at zero. Its corrected derivative
factors through a fixed Banach sequence exponent strictly below p/2,
throughout the whole complex action domain. The refined derivative depends
analytically on the action. Compactness still requires Pitt's theorem;
the derivative value at zero requires the first frequency Taylor coefficient.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Actual frequency maps with an analytic family of bounded derivatives
in a strictly refined target, and the exact corrected-derivative factorization. -/
theorem exists_sourceFrequency_smoothingDerivative (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ hp1 : 1 < p, ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), IsOpen V ∧ (0 : Coeff q) ∈ V ∧
      (∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      ∃ F : Coeff q → Coeff q, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧ F 0 = 0 ∧
        (∀ ψ : realTypeSourceSubmodule p, ∀ n,
          F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) ∧
        ∃ r : ℝ≥0∞, ∃ _ : Fact (1 ≤ r), r ≠ ⊤ ∧ 1 < r ∧
          ∃ hrq : r < q, ENNReal.ofReal (p.toReal/3) ≤ r ∧
          ∃ H : Coeff q → Coeff r, AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℝ H V ∧ H 0 = 0 ∧
            (∀ b ∈ V, ∀ n, H b n = F b n+2*b n) ∧
            AnalyticOnNhd ℂ (fderiv ℂ H) V ∧
            ∀ b ∈ V,
              fderiv ℂ F b + (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) =
                (Coeff.exponentInclusion hrq.le).comp (fderiv ℂ H b) ∧
              ∀ v : Coeff q,
                (∀ n, (fderiv ℂ H b v) n = (fderiv ℂ F b v) n+2*v n) ∧
                ‖fderiv ℂ F b v+(2 : ℂ) • v‖ ≤ ‖fderiv ℂ H b‖*‖v‖ := by
  have hp1 : 1 < p := lt_trans (by norm_num) hp2
  have hq : q ≠ ⊤ := Coeff.doublingExponent_ne_top hp
  obtain ⟨r,hr,hr1,hrq,hpr⟩ := Coeff.exists_strict_refined_actionExponent (q := q) hp hp2
  let instR : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hhalf : ENNReal.ofReal (p.toReal/2) = q := by
    calc
      ENNReal.ofReal (p.toReal/2) = ENNReal.ofReal q.toReal := by
        congr 1
        rw [Coeff.doublingExponent_toReal (p := p) (q := q)]
        ring
      _ = q := ENNReal.ofReal_toReal hq
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V,hV,hcenter,hpos,himage,hfreq⟩ :=
    exists_sourceFrequency_actionSpace_asymptotic (q := q) hp hp1 hp2.le
  obtain ⟨F,hF,hFR,hrec,hcorr,_⟩ := hfreq q hq (hr1.trans hrq) (by rw [hhalf])
  obtain ⟨H,hH,hHR,he⟩ := hcorr r hr hr1 hpr
  have hzero : (0 : Coeff q) ∈ V := by
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero] using hcenter 0
  have hFzero : F 0 = 0 := by
    ext n
    change F 0 n = 0
    have h := (hrec 0).2 n
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero,A.renormalizedFrequency_eq_zero_at_zero] using h
  have hHzero : H 0 = 0 := by
    ext n
    simpa only [hFzero,lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero] using he 0 hzero n
  refine ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,
    fun ψ => (hrec ψ).2,r,instR,hr,hr1,hrq,hpr,H,hH,hHR,hHzero,he,hH.fderiv,?_⟩
  intro b hb
  exact ⟨Coeff.actionCorrection_fderiv_factorization hrq.le V hV F H hF hH he b hb,
    fun v => Coeff.actionCorrection_fderiv_apply_bound hrq.le V hV F H hF hH he b hb v⟩

end NLS.ZakharovShabat
