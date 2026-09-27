import NLS.ZakharovShabat.SourceNormalizedActionFree
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Positive normalized action across collapsed real gaps

The normalized action is a continuous, real-valued, nonzero function
on the connected real-type source locus. Its free value is positive,
so its real part is positive everywhere, including at collapsed gaps.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex normalized-action extension has positive real part
at every real-type source, including a collapsed selected gap. -/
theorem sourceNormalizedActionComplexExtension_re_pos_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    0 < (sourceNormalizedActionComplexExtension hp hp1 n ψ).re := by
  let S := realTypeSourceLocus p
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  let g : CoeffPair p → ℝ := fun χ => (F χ).re
  have hconn : IsConnected (g '' S) := by
    apply isConnected_realTypeSourceLocus.image g
    intro χ hχ
    have hFcont : ContinuousAt F χ :=
      (differentiableAt_sourceNormalizedActionComplexExtension_of_realType
        hp hp1 χ hχ n).continuousAt
    exact (continuous_re.continuousAt.comp hFcont).continuousWithinAt
  have h0S : (0 : CoeffPair p) ∈ S := by
    simp [S,realTypeSourceLocus]
  have hg0 : g (0 : CoeffPair p) = 1/4 := by
    dsimp [g,F]
    rw [sourceNormalizedActionComplexExtension_zero_source hp hp1 n]
    norm_num
  have hψS : ψ ∈ S := hreal
  have hgψne : g ψ ≠ 0 := by
    intro he
    have hFne := sourceNormalizedActionComplexExtension_ne_zero_of_realType
      hp hp1 n ψ hreal
    have him := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType
      hp hp1 n ψ hreal
    apply hFne
    apply Complex.ext
    · exact he
    · exact him
  by_contra hnot
  have hle : g ψ ≤ 0 := le_of_not_gt hnot
  have hlt : g ψ < 0 := lt_of_le_of_ne hle hgψne
  have hψimage : g ψ ∈ g '' S := ⟨ψ,hψS,rfl⟩
  have h0image : g (0 : CoeffPair p) ∈ g '' S := ⟨0,h0S,rfl⟩
  have hzeroimage : (0:ℝ) ∈ g '' S :=
    hconn.Icc_subset hψimage h0image
      ⟨hlt.le, by rw [hg0]; norm_num⟩
  obtain ⟨χ,hχ,hχzero⟩ := hzeroimage
  have hχne := sourceNormalizedActionComplexExtension_ne_zero_of_realType
    hp hp1 n χ hχ
  have hχim := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType
    hp hp1 n χ hχ
  apply hχne
  apply Complex.ext
  · exact hχzero
  · exact hχim

/-- For each fixed index, the complex normalized action has positive
real part throughout one open neighborhood of the real-type locus.
The squared-gap factorization remains exact on that neighborhood. -/
theorem exists_global_sourceNormalizedActionComplexExtension_re_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) W ∧
      (∀ ψ ∈ W,
        0 < (sourceNormalizedActionComplexExtension hp hp1 n ψ).re) ∧
      ∀ ψ ∈ W,
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  let P : Set (CoeffPair p) := {ψ | ∃ U : Set (CoeffPair p),
    IsOpen U ∧ ψ ∈ U ∧ ∀ χ ∈ U, 0 < (F χ).re}
  have hPopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro ψ hψ
    obtain ⟨U,hUopen,hψU,hU⟩ := hψ
    exact Filter.mem_of_superset (hUopen.mem_nhds hψU)
      (fun χ hχ => ⟨U,hUopen,hχ,hU⟩)
  have hrealP : realTypeSourceLocus p ⊆ P := by
    intro ψ hreal
    have hpos : 0 < (F ψ).re :=
      sourceNormalizedActionComplexExtension_re_pos_of_realType
        hp hp1 n ψ hreal
    have hcont : ContinuousAt (fun χ : CoeffPair p => (F χ).re) ψ :=
      continuous_re.continuousAt.comp
        (differentiableAt_sourceNormalizedActionComplexExtension_of_realType
          hp hp1 ψ hreal n).continuousAt
    have hnear : ∀ᶠ χ : CoeffPair p in 𝓝 ψ, 0 < (F χ).re :=
      hcont.eventually (lt_mem_nhds hpos)
    obtain ⟨U,hUsub,hUopen,hψU⟩ := _root_.mem_nhds_iff.mp hnear
    exact ⟨U,hUopen,hψU,fun χ hχ => hUsub hχ⟩
  obtain ⟨D,hDopen,hrealD,hdiff,_,hfactor⟩ :=
    exists_global_sourceNormalizedActionComplexExtension_nonzero hp hp1 n
  let W := P ∩ D
  refine ⟨W,hPopen.inter hDopen,?_,hdiff.mono inter_subset_right,?_,?_⟩
  · intro ψ hreal
    exact ⟨hrealP hreal,hrealD hreal⟩
  · intro ψ hψ
    obtain ⟨U,_,hψU,hU⟩ := hψ.1
    exact hU ψ hψU
  · intro ψ hψ
    exact hfactor ψ hψ.2

/-- The principal square root of four times the complex normalized
action. Its regularity and nonvanishing hold on the positive-real-part
neighborhood constructed below. -/
def sourceNormalizedActionRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : CoeffPair p → ℂ :=
  fun ψ => Complex.sqrt (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)

/-- The square-root coordinate is complex Fréchet differentiable and
nonvanishing on a fixed-index complex neighborhood of all real-type
sources. Its square is four times the normalized action, and its free
value is one. -/
theorem exists_global_sourceNormalizedActionRoot_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      DifferentiableOn ℂ (sourceNormalizedActionRoot hp hp1 n) W ∧
      (∀ ψ ∈ W,
        sourceNormalizedActionRoot hp hp1 n ψ ≠ 0 ∧
        (sourceNormalizedActionRoot hp hp1 n ψ)^2 =
          4 * sourceNormalizedActionComplexExtension hp hp1 n ψ) ∧
      sourceNormalizedActionRoot hp hp1 n (0 : CoeffPair p) = 1 := by
  obtain ⟨W,hWopen,hrealW,hdiff,hpos,_⟩ :=
    exists_global_sourceNormalizedActionComplexExtension_re_pos hp hp1 n
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  have hslit (ψ : CoeffPair p) (hψ : ψ ∈ W) :
      4 * F ψ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have h := hpos ψ hψ
    simpa [Complex.mul_re, F] using mul_pos (by norm_num : (0:ℝ) < 4) h
  have hrootdiff : DifferentiableOn ℂ
      (sourceNormalizedActionRoot hp hp1 n) W := by
    intro ψ hψ
    have hF : DifferentiableAt ℂ F ψ :=
      (hdiff ψ hψ).differentiableAt (hWopen.mem_nhds hψ)
    have hinner : DifferentiableAt ℂ (fun χ => 4 * F χ) ψ :=
      hF.const_mul 4
    exact ((Complex.differentiableAt_sqrt (hslit ψ hψ)).comp ψ
      hinner).differentiableWithinAt
  refine ⟨W,hWopen,hrealW,hrootdiff,?_,?_⟩
  · intro ψ hψ
    have hsq : (Complex.sqrt (4 * F ψ))^2 = 4 * F ψ := by
      have h := Complex.cpow_nat_inv_pow (4 * F ψ) (Nat.succ_ne_zero 1)
      norm_num at h
      simpa only [Complex.sqrt, one_div] using h
    have hFne : F ψ ≠ 0 := by
      intro he
      have h := hpos ψ hψ
      change 0 < (F ψ).re at h
      rw [he] at h
      norm_num at h
    constructor
    · intro he
      change Complex.sqrt (4 * F ψ) = 0 at he
      rw [he] at hsq
      have hzero : (4:ℂ) * F ψ = 0 := by
        simpa using hsq.symm
      exact hFne ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
    · exact hsq
  · simp [sourceNormalizedActionRoot,
      sourceNormalizedActionComplexExtension_zero_source hp hp1 n]

/-- The square-root coordinate is analytic along every complex
source line through a real-type potential. -/
theorem analyticAt_sourceNormalizedActionRoot_alongLine_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (h : CoeffPair p) :
    AnalyticAt ℂ (fun t : ℂ =>
      sourceNormalizedActionRoot hp hp1 n (φ+t•h)) 0 := by
  obtain ⟨W,hWopen,hrealW,hdiff,_,_⟩ :=
    exists_global_sourceNormalizedActionRoot_differentiableOn hp hp1 n
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let U : Set ℂ := a ⁻¹' W
  have hUopen : IsOpen U := hWopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hrealW hreal
  have hline : DifferentiableOn ℂ
      (fun t : ℂ => sourceNormalizedActionRoot hp hp1 n (a t)) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt
      (hWopen.mem_nhds ht)).comp t (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

end NLS.ZakharovShabat
