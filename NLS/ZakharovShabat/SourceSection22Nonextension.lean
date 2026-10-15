import NLS.ZakharovShabat.SourceSection22Global
import NLS.ZakharovShabat.SourceOrdinaryTheorem22_1III
import NLS.ZakharovShabat.SmoothClassicalNLSNonextension
/-! # Original coordinate and physical source nonextension

Both complex coordinate obstructions use the physical phase orientation
and the actual original Birkhoff image. Source nonextension concerns
the all-smooth classical solution map on the forward interval [0,T].
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Theorem 22.1(iii): the first physical coordinate cannot extend at a non-Hilbert image point. -/
theorem coordinate_nonextension_fst (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k‖^2))
    (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0)
    (F : range (sourceRealBirkhoffMap hp hp1 s) → C(Icc (-T) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ τ : Icc (-T) T, F (D.complex.realImageHomeomorph ψ) τ =
        Complex.exp (((-τ.val*A.finiteGapOrdinaryFrequency ψ hf n : ℝ) : ℂ)*Complex.I)*
          (sourceComplexBirkhoffMap hp hp1 s ψ.val).1 n) :
    ¬ ContinuousAt F (D.complex.realImageHomeomorph φ) := by
  intro hF
  apply A.theorem22_1_iii_fst Q.roots D.roots_open D.roots_real_subset D.complex
    h2p T hT φ hφ n hn (fun z => (F z).comp (hamiltonianTimeReflection T))
    (fun ψ hf τ => ?_)
    ((ContinuousMap.continuous_precomp (hamiltonianTimeReflection T)).continuousAt.comp hF)
  simpa only [ContinuousMap.comp_apply,hamiltonianTimeReflection,ContinuousMap.coe_mk,neg_neg]
    using he ψ hf (hamiltonianTimeReflection T τ)

/-- Theorem 22.1(iii): the second physical coordinate has the same obstruction. -/
theorem coordinate_nonextension_snd (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p)
    (hφ : ¬ Summable (fun k : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k‖^2))
    (n : ℤ) (hn : (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n ≠ 0)
    (F : range (sourceRealBirkhoffMap hp hp1 s) → C(Icc (-T) T,ℂ))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ τ : Icc (-T) T, F (D.complex.realImageHomeomorph ψ) τ =
        Complex.exp (((τ.val*A.finiteGapOrdinaryFrequency ψ hf n : ℝ) : ℂ)*Complex.I)*
          (sourceComplexBirkhoffMap hp hp1 s ψ.val).2 n) :
    ¬ ContinuousAt F (D.complex.realImageHomeomorph φ) := by
  intro hF
  apply A.theorem22_1_iii_snd Q.roots D.roots_open D.roots_real_subset D.complex
    h2p T hT φ hφ n hn (fun z => (F z).comp (hamiltonianTimeReflection T))
    (fun ψ hf τ => ?_)
    ((ContinuousMap.continuous_precomp (hamiltonianTimeReflection T)).continuousAt.comp hF)
  simpa only [ContinuousMap.comp_apply,hamiltonianTimeReflection,ContinuousMap.coe_mk]
    using he ψ hf (hamiltonianTimeReflection T τ)

/-- Corollary 22.2(iii), using the original source family and constructed original
Hilbert and target families. Agreement on actual finite-gap classical solutions suffices. -/
theorem finiteGap_source_nonextension
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithFiniteGapClassicalNLS hp hp1 T F) : ¬ ContinuousAt F φ := by
  obtain ⟨W₀₂,W₂,V₂,s₂,D₂,Wa₂,H,B₂,U₂,Q₂⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  obtain ⟨W₀q,Wq,Vq,sq,Dq,Waq,Aq,Bq,Uq,Qq⟩ := sourceSection20_original hq hq1
  apply A.not_continuousAt_hamiltonianSource_extension Q.roots D.roots_open D.roots_real_subset
    D.complex H Q₂.roots.toSourcePsiIsolatingComplexExtension D₂.complex Dq.complex
    h2p h2q T hT φ hφ F
  intro ψ hf τ
  obtain ⟨u,hu,hinit,hcoeff⟩ := hF ψ hf
  apply realTypeSource_eq_of_fst
  intro n
  exact (hcoeff τ n).trans
    (H.periodOneCoefficient_classicalNLS_eq_hamiltonianFlow Q₂.roots.toSourcePsiIsolatingComplexExtension
      D₂.complex hp hp1 ψ hf u hu hinit τ.val n)

/-- The original forward-time obstruction applies to extensions of the all-smooth
classical solution map; in particular this covers every finite target q ≥ p > 2. -/
theorem smooth_source_nonextension
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (0 : ℝ) T) F) : ¬ ContinuousAt F φ :=
  Q.finiteGap_source_nonextension hq hq1 h2p h2q T hT φ hφ F
    ((agreesWithFiniteGapClassicalNLS_iff hp hp1 T F).mpr (hF.finiteGap_coefficients hp hp1))

/-- The same original obstruction on symmetric compact time intervals. -/
theorem smooth_source_nonextension_symmetric
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (-T) T) F) : ¬ ContinuousAt F φ := by
  intro hcont
  let r : C(Icc (0 : ℝ) T,Icc (-T) T) :=
    ⟨fun τ => ⟨τ.val,by constructor; linarith [τ.property.1]; exact τ.property.2⟩,
      by fun_prop⟩
  exact Q.smooth_source_nonextension hq hq1 h2p h2q T hT φ hφ
    (fun ψ => (F ψ).comp r) (fun f τ => hF f (r τ))
    ((ContinuousMap.continuous_precomp r).continuousAt.comp hcont)
end NLS.ZakharovShabat.SourceSection20Data
