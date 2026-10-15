import NLS.ZakharovShabat.SourceSection20Moments
import NLS.ZakharovShabat.SourceFrequencyOriginalPhysical

/-!
# The original Section 20 frequency map

The actual source frequency has compatible analytic sequence realizations,
agrees across source exponents, and recovers the original action frequency.
The latter equality also holds on a common connected complex source domain.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Theorem 20.5: all sequence coordinates are actual scalar frequencies,
and both complex and real analyticity hold on the same source domain. -/
theorem sequence_analytic (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
    AnalyticOnNhd ℂ (A.frequencySequence r) U ∧ AnalyticOnNhd ℝ (A.frequencySequence r) U ∧
    ∀ φ : realTypeSourceSubmodule p, ∀ n, (A.frequencySequence r φ.val n).im = 0 := by
  obtain ⟨he,ha⟩ := Q.sequence r hr hr1 hpr
  refine ⟨he,ha,ha.restrictScalars,?_⟩
  intro φ n
  rw [he φ.val (Q.real_subset φ.property) n]
  exact Q.frequency_real φ n

/-- The zero source gives the zero sequence, with no constructor fallback. -/
theorem sequence_zero (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) : A.frequencySequence r 0 = 0 := by
  ext n
  rw [(Q.sequence r hr hr1 hpr).1 0 (Q.real_subset (by simp [realTypeSourceLocus])) n]
  exact A.renormalizedFrequency_eq_zero_at_zero n

/-- Equal Fourier coefficients give equal actual scalar frequencies,
even with independently constructed original roots and moment atlases. -/
theorem frequency_eq_of_coefficients
    {p' : ℝ≥0∞} [Fact (1 ≤ p')] {hp' : p' ≠ ⊤} {hp1' : 1 < p'}
    {W₀' W' V' Wa' B' U' : Set (CoeffPair p')}
    {s' : (n : ℤ) → CoeffPair p' → DeletedCoeff p' n}
    {D' : SourceSection17OriginalData hp' hp1' W₀' W' V' s'}
    {A' : SourceAbelianMomentAtlas hp' hp1' Wa' s'} (Q' : SourceSection20Data D' A' B' U')
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule p')
    (he : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) (n : ℤ) :
    A.renormalizedFrequency n φ.val = A'.renormalizedFrequency n ψ.val :=
  A.renormalizedFrequency_real_eq_of_coefficients A' Q.roots.toSourcePsiIsolatingComplexExtension
    Q'.roots.toSourcePsiIsolatingComplexExtension φ ψ he n

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderTriple p q]
  {T : Set (Coeff q)} {F : Coeff q → Coeff q}

/-- The new original moment sum recovers any previously chosen original
Section 18 action frequency on the entire real locus. -/
theorem action_frequency (E : SourceOriginalFrequencyData D T F)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    F (sourceActionSequence hp hp1 s φ.val) n = A.renormalizedFrequency n φ.val := by
  obtain ⟨Wb,sb,C,P,hs,he⟩ := E.spectral
  exact (he φ n).trans (C.renormalizedFrequency_real_eq_of_coefficients A hs
    Q.roots.toSourcePsiIsolatingComplexExtension φ φ (fun _ => ⟨rfl,rfl⟩) n)

/-- Source and action frequencies agree throughout a common connected
complex neighborhood, retaining every real source and every coordinate. -/
theorem action_frequency_complex (E : SourceOriginalFrequencyData D T F) :
    ∃ Y : Set (CoeffPair p), IsOpen Y ∧ IsConnected Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ U ∧
      (∀ ψ ∈ Y, sourceActionSequence (q := q) hp hp1 s ψ ∈ T) ∧
      ∀ ψ ∈ Y, ∀ n, F (sourceActionSequence hp hp1 s ψ) n = A.renormalizedFrequency n ψ := by
  let J := U ∩ sourceActionSequence (q := q) hp hp1 s ⁻¹' T
  have hJ : IsOpen J :=
    (D.complex.actionSequence_analytic.mono Q.original_subset).continuousOn.isOpen_inter_preimage Q.source_open E.isOpen
  have hrealJ : realTypeSourceLocus p ⊆ J :=
    fun ψ hψ => ⟨Q.real_subset hψ,E.real_actions_mem ⟨ψ,hψ⟩⟩
  have hz : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  let Y := connectedComponentIn J (0 : CoeffPair p)
  have hY : IsOpen Y := hJ.connectedComponentIn
  have hconn : IsConnected Y := isConnected_connectedComponentIn_iff.mpr (hrealJ hz)
  have hsub : Y ⊆ J := connectedComponentIn_subset J 0
  have hreal : realTypeSourceLocus p ⊆ Y :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz hrealJ
  refine ⟨Y,hY,hconn,hreal,fun ψ hψ => (hsub hψ).1,fun ψ hψ => (hsub hψ).2,?_⟩
  have he (n : ℤ) : EqOn (fun ψ => F (sourceActionSequence hp hp1 s ψ) n) (A.renormalizedFrequency n) Y := by
    have ha : AnalyticOnNhd ℂ (fun ψ => F (sourceActionSequence hp hp1 s ψ) n) Y := by
      intro ψ hψ
      exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).analyticAt _).comp
        ((E.analytic _ (hsub hψ).2).comp (D.complex.actionSequence_analytic ψ (Q.original_subset (hsub hψ).1)))
    apply eqOn_of_analytic_of_sourceFiniteGap hp hp1 hY hconn hreal ha
      ((Q.frequency_analytic n).mono (fun ψ hψ => (hsub hψ).1))
    intro φ _
    exact Q.action_frequency E φ n
  exact fun ψ hψ n => he n hψ

end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.ZakharovShabat.SourceSection20Data

/-- The original Hilbert action frequency is the same original moment sum. -/
theorem hilbert_action_frequency
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection20Data D A B U) {T : Set (Coeff 1)} {F : Coeff 1 → ℤ → ℂ}
    (E : SourceOriginalHilbertFrequencyData D T F) (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    F (sourceActionSequence (q := 1) (by simp) (by norm_num) s φ.val) n = A.renormalizedFrequency n φ.val := by
  obtain ⟨Wb,sb,C,P,hs,he⟩ := E.spectral
  exact (he φ n).trans (C.renormalizedFrequency_real_eq_of_coefficients A hs
    Q.roots.toSourcePsiIsolatingComplexExtension φ φ (fun _ => ⟨rfl,rfl⟩) n)

end NLS.ZakharovShabat.SourceSection20Data
