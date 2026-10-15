import NLS.ZakharovShabat.SourceFrequencyOriginalInverse
import NLS.ZakharovShabat.SourceFrequencyTheorem18_1Real

/-!
# The common Hilbert frequency and all original-family extensions

One frequency on summable actions has all real sequence-space realizations.
Every higher-exponent original family extends those same values, retaining
the mixed remainder and all the inverse conclusions for its one chosen map.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original Hilbert action frequency, with a common domain for every r>1. -/
structure SourceOriginalHilbertFrequencyData
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    (U : Set (Coeff 1)) (ωstar : Coeff 1 → ℤ → ℂ) : Prop where
  isOpen : IsOpen U
  isPreconnected : IsPreconnected U
  zero_mem : (0 : Coeff 1) ∈ U
  real_actions_mem : ∀ φ : realTypeSourceSubmodule 2,
    sourceActionSequence (q := 1) (by simp) (by norm_num) s φ.val ∈ U
  positive_actions_mem : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → RealCoeff.complexCLM 1 b ∈ U
  source_image : ∃ Y : Set (CoeffPair 2), IsOpen Y ∧ realTypeSourceLocus 2 ⊆ Y ∧ Y ⊆ V ∧
    sourceActionSequence (q := 1) (by simp) (by norm_num) s '' Y = U
  spectral : ∃ Wa : Set (CoeffPair 2), ∃ sa : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
    ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa sa,
    ∃ P : Set (CoeffPair 2), SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P sa ∧
      ∀ φ : realTypeSourceSubmodule 2, ∀ n,
        ωstar (sourceActionSequence (q := 1) (by simp) (by norm_num) s φ.val) n = A.renormalizedFrequency n φ.val
  realizations : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
    ∃ F : Coeff 1 → Coeff r, AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℝ F U ∧
      (∀ b ∈ U, ∀ n, F b n = ωstar b n) ∧
      ∃ R : RealCoeff 1 → RealCoeff r, AnalyticOnNhd ℝ R (RealCoeff.complexCLM 1 ⁻¹' U) ∧
        ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n, (R b n : ℂ) = ωstar (RealCoeff.complexCLM 1 b) n

/-- Construct the common Hilbert frequency for any original Hilbert family. -/
theorem SourceSection17OriginalData.exists_hilbert_frequency
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s) :
    ∃ U : Set (Coeff 1), ∃ ωstar : Coeff 1 → ℤ → ℂ, SourceOriginalHilbertFrequencyData D U ωstar := by
  obtain ⟨Wa,sa,A,P,hs,X₀,B,X,t,E,T,ωstar,hT,_,hcenter,hfamily,_⟩ :=
    exists_sourceFrequency_theorem18_1_real
  have he (φ : realTypeSourceSubmodule 2) : sourceActionSequence (q := 1) (by simp) (by norm_num) s φ.val =
      sourceActionSequence (by simp) (by norm_num) t φ.val :=
    D.actionSequence_eq E φ.val (D.complex.real_subset φ.property) (E.real_subset φ.property)
  obtain ⟨U,hU,hconn,hzero,hUT,hreal,hpos,himage⟩ :=
    D.exists_connected_action_image le_rfl T hT (fun φ => (he φ).symm ▸ (hcenter φ).1)
  refine ⟨U,ωstar,hU,hconn,hzero,hreal,?_,himage,
    ⟨Wa,sa,A,P,hs,fun φ n => by rw [he φ]; exact (hcenter φ).2 n⟩,?_⟩
  · intro b hb
    have hi : Coeff.exponentInclusion (le_refl (1 : ℝ≥0∞)) (RealCoeff.complexCLM 1 b) =
        RealCoeff.complexCLM 1 b := by ext n; rfl
    simpa only [hi] using hpos b hb
  · intro r inst hr hr1
    obtain ⟨F,hF,hFR,hval,R,hR,hRval⟩ := hfamily r hr hr1
    exact ⟨F,hF.mono hUT,hFR.mono hUT,fun b hb => hval b (hUT hb),
      R,hR.mono (fun _ hb => hUT hb),hRval⟩

/-- Every higher-exponent extension agrees with the fixed Hilbert frequency
on the full nonnegative summable cone, independently of all atlas choices. -/
theorem SourceOriginalFrequencyData.eq_hilbert_on_positive
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {D : SourceSection17OriginalData hp hp1 W₀ W V s} {U : Set (Coeff q)} {F : Coeff q → Coeff q}
    (E : SourceOriginalFrequencyData D U F) (h2p : 2 ≤ p)
    {W₂ B₂ V₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D₂ : SourceSection17OriginalData (by simp) (by norm_num) W₂ B₂ V₂ s₂}
    {U₂ : Set (Coeff 1)} {ωstar : Coeff 1 → ℤ → ℂ}
    (H : SourceOriginalHilbertFrequencyData D₂ U₂ ωstar)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) (n : ℤ) :
    F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) n =
      ωstar (RealCoeff.complexCLM 1 b) n := by
  obtain ⟨Wa,sa,A,P,hs,hrec⟩ := E.spectral
  obtain ⟨Wb,sb,A₂,P₂,hs₂,hrec₂⟩ := H.spectral
  have h := A.actionMap_eq_on_nonnegative_summable A₂ hs hs₂ D.complex D₂.complex h2p le_rfl
    (fun c k => F c k) ωstar hrec hrec₂ b hb n
  have hi : Coeff.exponentInclusion (le_refl (1 : ℝ≥0∞)) (RealCoeff.complexCLM 1 b) =
      RealCoeff.complexCLM 1 b := by ext k; rfl
  simpa only [hi] using h

/-- Theorem 18.1 and Corollary 18.2 share one constructed higher-exponent
map for every original family, extending a single original Hilbert frequency. -/
theorem sourceSection18_original_frequencies :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ U₂ : Set (Coeff 1), ∃ ωstar : Coeff 1 → ℤ → ℂ,
      SourceOriginalHilbertFrequencyData D U₂ ωstar ∧
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
        (hp : p ≠ ⊤) (hp1 : 1 < p) (_hp2 : 2 < p)
        (W₀ W V : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
        (D : SourceSection17OriginalData hp hp1 W₀ W V s),
        ∃ U : Set (Coeff q), ∃ F : Coeff q → Coeff q, SourceOriginalFrequencyData D U F ∧
          ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∀ n,
            F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) n =
              ωstar (RealCoeff.complexCLM 1 b) n := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original (p := 2) (by simp) (by norm_num)
  obtain ⟨U₂,ωstar,H⟩ := D.exists_hilbert_frequency
  refine ⟨W₀,W,V,s,D,U₂,ωstar,H,?_⟩
  intro p q instP instQ instPQ hp hp1 hp2 W₀ W V s D
  obtain ⟨U,F,E⟩ := D.exists_frequency_asymptotic (q := q) hp2
  exact ⟨U,F,E,fun b hb n => E.eq_hilbert_on_positive hp2.le H b hb n⟩

end NLS.ZakharovShabat
