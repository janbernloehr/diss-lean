import NLS.ZakharovShabat.SourceOriginalActionImage
import NLS.ZakharovShabat.SourceFrequencyActionSpaceAsymptotic
import NLS.SequenceSpaces.RefinedActionExponent

/-!
# One action frequency for the original family

The actual moment frequency, all refined analytic corrections, and the
locally uniform mixed remainder share one connected action domain. Its
source image uses the original Section 17 family.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Theorem 18.1 data for one map on an action image of the original family. -/
structure SourceOriginalFrequencyData
    (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    (U : Set (Coeff q)) (F : Coeff q → Coeff q) : Prop where
  isOpen : IsOpen U
  isPreconnected : IsPreconnected U
  zero_mem : (0 : Coeff q) ∈ U
  real_actions_mem : ∀ φ : realTypeSourceSubmodule p, sourceActionSequence hp hp1 s φ.val ∈ U
  positive_actions_mem : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
    Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ U
  source_image : ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ V ∧
    sourceActionSequence (q := q) hp hp1 s '' Y = U
  analytic : AnalyticOnNhd ℂ F U
  map_zero : F 0 = 0
  spectral : ∃ Wa : Set (CoeffPair p), ∃ sa : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 Wa sa,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P sa ∧
      ∀ φ : realTypeSourceSubmodule p, ∀ n,
        F (sourceActionSequence hp hp1 s φ.val) n = A.renormalizedFrequency n φ.val
  refined : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
    ∃ H : Coeff q → Coeff r, AnalyticOnNhd ℂ H U ∧ AnalyticOnNhd ℝ H U ∧
      ∀ b ∈ U, ∀ n, H b n = F b n+2*b n
  mixed : ∀ b ∈ U, ∃ T : Set (Coeff q), IsOpen T ∧ b ∈ T ∧ T ⊆ U ∧
    ∃ g : Coeff q → Coeff (ENNReal.ofReal (p.toReal/3)), ∃ h : Coeff q → CoeffOnePlus,
      (∀ c ∈ T, ∀ n, F c n+2*c n = g c n+(h c).1 n) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖g c‖ ≤ M) ∧
      ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖CoeffOnePlus.toCoeff r hr1 hr (h c)‖ ≤ M

/-- Every original family admits the actual frequency with all Theorem 18.1
remainders on one connected action image retaining the whole real locus. -/
theorem SourceSection17OriginalData.exists_frequency_asymptotic
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) (hp2 : 2 < p) :
    ∃ U : Set (Coeff q), ∃ F : Coeff q → Coeff q, SourceOriginalFrequencyData D U F := by
  obtain ⟨Wa,sa,A,P,hs,X₀,B,X,t,E,T,hT,hcenter,_,_,hfreq⟩ :=
    exists_sourceFrequency_actionSpace_asymptotic (q := q) hp hp1 hp2.le
  have hq : q ≠ ⊤ := Coeff.doublingExponent_ne_top hp
  obtain ⟨r,_,hr1,hrq,_⟩ := Coeff.exists_strict_refined_actionExponent (q := q) hp hp2
  have hhalf : ENNReal.ofReal (p.toReal/2) = q := by
    calc
      ENNReal.ofReal (p.toReal/2) = ENNReal.ofReal q.toReal := by
        congr 1
        rw [Coeff.doublingExponent_toReal (p := p) (q := q)]
        ring
      _ = q := ENNReal.ofReal_toReal hq
  obtain ⟨F,hF,_,hrec,hcorr,hlocal⟩ := hfreq q hq (hr1.trans hrq) (by rw [hhalf])
  have he (φ : realTypeSourceSubmodule p) : sourceActionSequence (q := q) hp hp1 s φ.val =
      sourceActionSequence hp hp1 t φ.val :=
    D.actionSequence_eq E φ.val (D.complex.real_subset φ.property) (E.real_subset φ.property)
  obtain ⟨U,hU,hconn,hzero,hUT,hreal,hpos,himage⟩ :=
    D.exists_connected_action_image hp2.le T hT (fun φ => (he φ).symm ▸ hcenter φ)
  have hFzero : F 0 = 0 := by
    ext n
    change F 0 n = 0
    have h := (hrec 0).2 n
    simpa only [ZeroMemClass.coe_zero,E.actionSequence_zero,A.renormalizedFrequency_eq_zero_at_zero] using h
  refine ⟨U,F,hU,hconn,hzero,hreal,hpos,himage,hF.mono hUT,hFzero,
    ⟨Wa,sa,A,P,hs,fun φ n => by rw [he φ]; exact (hrec φ).2 n⟩,?_,?_⟩
  · intro u inst hu hu1 hpu
    obtain ⟨H,hH,hHR,hHval⟩ := hcorr u hu hu1 hpu
    exact ⟨H,hH.mono hUT,hHR.mono hUT,fun b hb => hHval b (hUT hb)⟩
  · intro b hb
    obtain ⟨L,hL,hbL,_,_,g,h,hval,⟨M,hM,hbound⟩,hplus⟩ := hlocal b (hUT hb)
    refine ⟨L ∩ U,hL.inter hU,⟨hbL,hb⟩,inter_subset_right,g,h,
      fun c hc => hval c hc.1,⟨M,hM,fun c hc => hbound c hc.1⟩,?_⟩
    intro u hu1 hu
    obtain ⟨K,hK,hKbound⟩ := hplus u hu1 hu
    exact ⟨K,hK,fun c hc => hKbound c hc.1⟩

end NLS.ZakharovShabat
