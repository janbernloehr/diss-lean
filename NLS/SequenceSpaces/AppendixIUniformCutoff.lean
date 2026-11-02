import NLS.SequenceSpaces.WeightedSourceLemmaI3
import NLS.SequenceSpaces.SourceCompactProjection
import NLS.SequenceSpaces.WeightedRealAnalyticAtlas
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Uniform weighted output cutoffs in Appendix I

The omitted frequencies are exactly |n| > N. Compactness at one parameter
gives the stated quarter bound, and continuity gives the half bound nearby.
On a compact parameter set one cutoff works on an open neighborhood, even
when compactness of the operators is assumed only on the compact set.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {X : Type*} [TopologicalSpace X]

/-- The source's weighted complementary projection as a bounded operator. -/
def appendixI_tailOperator (w : Weight) (N : ℕ) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.sourceI3Tail N).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The operator retains exactly the weighted tail in Lemma I.3. -/
@[simp] theorem appendixI_tailOperator_apply (w : Weight) (N : ℕ) (a : WeightedCoeff w p) :
    appendixI_tailOperator w N a = sourceI3Tail w N a := by
  apply (weightEquiv w p).injective
  rw [weightEquiv_sourceI3Tail]
  exact (weightEquiv w p).apply_symm_apply _

/-- Increasing the cutoff decreases the whole output-tail operator norm. -/
theorem appendixI_norm_tailOperator_comp_antitone (w : Weight) (T : E →L[ℂ] WeightedCoeff w p) :
    Antitone (fun N => ‖(appendixI_tailOperator w N).comp T‖) := by
  intro M N hMN
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖(appendixI_tailOperator w N).comp T x‖
        ≤ ‖(appendixI_tailOperator w M).comp T x‖ := by
          simp only [ContinuousLinearMap.comp_apply,appendixI_tailOperator_apply,norm_sourceI3Tail]
          exact Coeff.norm_sourceI3Tail_antitone _ hMN
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ x

/-- The lower block acts on the tail subspace, and its norm is bounded by the full output tail. -/
theorem appendixI_tail_block_norm (w : Weight) (N : ℕ)
    (T : WeightedCoeff w p →L[ℂ] WeightedCoeff w p) :
    ∃ D : (appendixI_tailOperator (p := p) w N).range →L[ℂ]
        (appendixI_tailOperator (p := p) w N).range,
      (∀ y, (D y).val = appendixI_tailOperator w N (T y.val)) ∧
      ‖D‖ ≤ ‖(appendixI_tailOperator w N).comp T‖ := by
  let Y : Submodule ℂ (WeightedCoeff w p) := (appendixI_tailOperator w N).range
  let D : Y →L[ℂ] Y := (((appendixI_tailOperator w N).comp T).comp Y.subtypeL).codRestrict Y
    (fun y => ⟨T y.val,rfl⟩)
  refine ⟨D,fun _ => rfl,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  exact ContinuousLinearMap.le_opNorm ((appendixI_tailOperator w N).comp T) y.val

/-- Compact weighted outputs admit one cutoff for all unit inputs and all larger cutoffs. -/
theorem appendixI_compact_tail_cutoff (hp : p ≠ ⊤) (w : Weight)
    (T : E →L[ℂ] WeightedCoeff w p) (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ M : ℕ, N ≤ M → ‖(appendixI_tailOperator w M).comp T‖ ≤ ε := by
  have hK := hT.isCompact_closure_image_closedBall 1
  obtain ⟨N,hN,hbound⟩ := ((sourceLemmaI3 hp w _).mp hK.totallyBounded).2 ε hε
  have hnorm : ‖(appendixI_tailOperator w N).comp T‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
    intro x hx
    simp only [ContinuousLinearMap.comp_apply,appendixI_tailOperator_apply]
    exact hbound (T x) (subset_closure ⟨x,by
      simpa only [mem_closedBall,dist_zero_right,hx] using (le_rfl : (1 : ℝ) ≤ 1),rfl⟩)
  exact ⟨N,hN,fun M hM => (appendixI_norm_tailOperator_comp_antitone w T hM).trans hnorm⟩

/-- The quarter bound at a compact operator gives the half bound on a parameter neighborhood. -/
theorem appendixI_local_tail_cutoff (hp : p ≠ ⊤) (w : Weight)
    (T : X → E →L[ℂ] WeightedCoeff w p) {z : X}
    (hc : ContinuousAt T z) (hT : IsCompactOperator (T z)) :
    ∃ N : ℕ, 1 ≤ N ∧ ‖(appendixI_tailOperator w N).comp (T z)‖ ≤ 1/4 ∧
      ∀ᶠ y in 𝓝 z, ∀ M : ℕ, N ≤ M → ‖(appendixI_tailOperator w M).comp (T y)‖ ≤ 1/2 := by
  obtain ⟨N,hN,hbound⟩ := appendixI_compact_tail_cutoff hp w (T z) hT (ε := 1/4) (by norm_num)
  have hcont : ContinuousAt (fun y => ‖(appendixI_tailOperator w N).comp (T y)‖) z :=
    (((ContinuousLinearMap.compL ℂ E (WeightedCoeff w p) (WeightedCoeff w p))
      (appendixI_tailOperator w N)).continuous.continuousAt.comp hc).norm
  have hsmall : ‖(appendixI_tailOperator w N).comp (T z)‖ < 1/2 :=
    (hbound N le_rfl).trans_lt (by norm_num)
  refine ⟨N,hN,hbound N le_rfl,?_⟩
  filter_upwards [hcont (gt_mem_nhds hsmall)] with y hy
  exact fun M hM => (appendixI_norm_tailOperator_comp_antitone w (T y) hM).trans hy.le

/-- A single cutoff controls an open neighborhood of a compact parameter set.
Compactness of the operators is required only on the compact set. -/
theorem appendixI_compact_family_tail_cutoff (hp : p ≠ ⊤) (w : Weight)
    (T : X → E →L[ℂ] WeightedCoeff w p) {U K : Set X}
    (hU : IsOpen U) (hc : ContinuousOn T U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hT : ∀ z ∈ K, IsCompactOperator (T z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ z ∈ V, ∀ M : ℕ, N ≤ M → ‖(appendixI_tailOperator w M).comp (T z)‖ < ε := by
  let V : ℕ → Set X := fun N => {z ∈ U | ‖(appendixI_tailOperator w N).comp (T z)‖ < ε}
  have hopen (N : ℕ) : IsOpen (V N) := by
    have hcont : ContinuousOn (fun z => ‖(appendixI_tailOperator w N).comp (T z)‖) U :=
      (((ContinuousLinearMap.compL ℂ E (WeightedCoeff w p) (WeightedCoeff w p))
        (appendixI_tailOperator w N)).continuous.comp_continuousOn hc).norm
    exact hcont.isOpen_inter_preimage hU isOpen_Iio
  have hmono : Monotone V := by
    intro M N hMN z hz
    exact ⟨hz.1,(appendixI_norm_tailOperator_comp_antitone w (T z) hMN).trans_lt hz.2⟩
  have hcover : K ⊆ ⋃ N, V N := by
    intro z hz
    obtain ⟨N,_,hbound⟩ := appendixI_compact_tail_cutoff hp w (T z) (hT z hz) (half_pos hε)
    exact mem_iUnion.mpr ⟨N,hKU hz,(hbound N le_rfl).trans_lt (half_lt_self hε)⟩
  obtain ⟨N,hN⟩ := hK.elim_directed_cover V hopen hcover hmono.directed_le
  refine ⟨max 1 N,le_max_left _ _,V (max 1 N),hopen _,
    hN.trans (hmono (le_max_right _ _)),fun _ hz => hz.1,?_⟩
  intro z hz M hM
  exact (appendixI_norm_tailOperator_comp_antitone w (T z) hM).trans_lt hz.2

/-- The real source atlas supplies the ambient complex neighborhood in I.4.
Its constructed complex germ has the original complexified derivative at the center. -/
theorem NonnegativeRealAnalyticAtlas.appendixI_local_derivative_cutoff
    (hp : p ≠ ⊤) {w : Weight} {f : nonnegativeLocus w p → WeightedRealCoeff w p}
    {U : Set (nonnegativeLocus w p)} (a : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U)
    (hcompact : IsCompactOperator
      (a.complexifiedDerivative x - 1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    ∃ N : ℕ, 1 ≤ N ∧
      ‖(appendixI_tailOperator w N).comp (a.complexifiedDerivative x - 1)‖ ≤ 1/4 ∧
      ∀ᶠ y in 𝓝 x.val, ∀ M : ℕ, N ≤ M →
        ‖(appendixI_tailOperator w M).comp (fderiv ℂ (a.toComplex.extension x) y - 1)‖ ≤ 1/2 := by
  have hcenter : fderiv ℂ (a.toComplex.extension x) x.val = a.complexifiedDerivative x :=
    a.toComplex_derivative hx
  have hcont : ContinuousAt (fun y => fderiv ℂ (a.toComplex.extension x) y - 1) x.val :=
    (a.toComplex.analyticAt x hx).fderiv.continuousAt.sub continuousAt_const
  obtain ⟨N,hN,hbound,hnear⟩ := appendixI_local_tail_cutoff hp w
    (fun y => fderiv ℂ (a.toComplex.extension x) y - 1) hcont (by rwa [hcenter])
  exact ⟨N,hN,by rwa [hcenter] at hbound,hnear⟩

/-- One Fourier cutoff controls the complex germs along a compact part of the real cone.
The quarter bound holds on a relative neighborhood; each center has an ambient
complex neighborhood with the half bound, using that same cutoff. -/
theorem NonnegativeRealAnalyticAtlas.appendixI_compact_derivative_cutoff
    (hp : p ≠ ⊤) {w : Weight} {f : nonnegativeLocus w p → WeightedRealCoeff w p}
    {U K : Set (nonnegativeLocus w p)} (a : NonnegativeRealAnalyticAtlas f U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcompact : ∀ x ∈ K, IsCompactOperator
      (a.complexifiedDerivative x - 1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (nonnegativeLocus w p),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      (∀ x ∈ V, ∀ M : ℕ, N ≤ M →
        ‖(appendixI_tailOperator w M).comp (a.complexifiedDerivative x - 1)‖ < 1/4) ∧
      ∀ x ∈ K, ∀ᶠ y in 𝓝 x.val, ∀ M : ℕ, N ≤ M →
        ‖(appendixI_tailOperator w M).comp (fderiv ℂ (a.toComplex.extension x) y - 1)‖ ≤ 1/2 := by
  have hc : ContinuousOn (fun x => a.complexifiedDerivative x - 1) U := by
    intro x hx
    obtain ⟨g,hg,he⟩ := a.toComplex.derivative_hasLocalAnalyticExtensions hp hU x hx
    have hd := (hg.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq he
    have heq : a.complexifiedDerivative =ᶠ[𝓝 x] a.toComplex.derivative := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (a.toComplex_derivative hy).symm
    exact ((hd.congr_of_eventuallyEq heq).sub continuousAt_const).continuousWithinAt
  obtain ⟨N,hN,V,hV,hKV,hVU,hbound⟩ := appendixI_compact_family_tail_cutoff hp w
    (fun x => a.complexifiedDerivative x - 1) hU hc hK hKU hcompact (ε := 1/4) (by norm_num)
  refine ⟨N,hN,V,hV,hKV,hVU,hbound,?_⟩
  intro x hx
  have hcenter : fderiv ℂ (a.toComplex.extension x) x.val = a.complexifiedDerivative x :=
    a.toComplex_derivative (hKU hx)
  have hcont : ContinuousAt (fun y =>
      ‖(appendixI_tailOperator w N).comp (fderiv ℂ (a.toComplex.extension x) y - 1)‖) x.val :=
    (((ContinuousLinearMap.compL ℂ (WeightedCoeff w p) (WeightedCoeff w p) (WeightedCoeff w p))
      (appendixI_tailOperator w N)).continuous.continuousAt.comp
        ((a.toComplex.analyticAt x (hKU hx)).fderiv.continuousAt.sub continuousAt_const)).norm
  have hsmall : ‖(appendixI_tailOperator w N).comp
      (fderiv ℂ (a.toComplex.extension x) x.val - 1)‖ < 1/2 := by
    rw [hcenter]
    exact (hbound x (hKV hx) N le_rfl).trans (by norm_num)
  filter_upwards [hcont (gt_mem_nhds hsmall)] with y hy
  exact fun M hM => (appendixI_norm_tailOperator_comp_antitone w _ hM).trans hy.le

end NLS.WeightedCoeff
