import NLS.Fourier.IntrinsicGraphClosed
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Completeness of the intrinsic interval Sobolev space

The physical graph is a closed linear subspace of two complete `L²` spaces.
Consequently the exact intrinsic norm is complete, including at half regularity.
Its inner product is the sum of the physical `L²` and difference-quotient inner
products, so the intrinsic interval space is a complex Hilbert space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace NLS.Fourier.IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

/-- The physical graph is a linear isometric embedding for the intrinsic norm. -/
def graphIsometry : IntrinsicIntervalSobolev s L →ₗᵢ[ℂ]
    WithLp 2 (CircleL2 × Lp ℂ 2 (intervalProductMeasure L)) where
  toLinearMap := graph
  norm_map' _ := rfl

/-- The image of the physical graph is closed in the product of `L²` spaces. -/
theorem isClosed_range_graph : IsClosed (range (graph (s := s) (L := L))) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u z hu hz
  choose f hf using hu
  have hL : 0 < L := Fact.out
  have hc : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  let F : CircleL2 := (Real.sqrt L : ℂ)⁻¹ • z.fst
  have hval : (fun n => (f n).val) = fun n => (Real.sqrt L : ℂ)⁻¹ • (u n).fst := by
    funext n
    rw [← hf n]
    change (f n).val = (Real.sqrt L : ℂ)⁻¹ • ((Real.sqrt L : ℂ) • (f n).val)
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hF : Tendsto (fun n => (f n).val) atTop (𝓝 F) := by
    rw [hval]
    exact tendsto_const_nhds.smul (((WithLp.continuous_fst 2 _ _).tendsto z).comp hz)
  have hG : Tendsto (fun n => quotient (f n)) atTop (𝓝 z.snd) := by
    have he : (fun n => quotient (f n)) = fun n => (u n).snd := by
      funext n
      rw [← hf n]
      rfl
    rw [he]
    exact ((WithLp.continuous_snd 2 _ _).tendsto z).comp hz
  have he : fractionalDifferenceQuotient s (intervalPullback L F) =ᵐ[intervalProductMeasure L] z.snd :=
    fractionalDifferenceQuotient_closed hL hF hG (fun n => (f n).property.coeFn_toLp)
  have hmem : MemLp (fractionalDifferenceQuotient s (intervalPullback L F)) 2 (intervalProductMeasure L) :=
    (memLp_congr_ae he).mpr (Lp.memLp z.snd)
  let a : IntrinsicIntervalSobolev s L := ⟨F, hmem⟩
  have hquot : quotient a = z.snd := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans he
  refine ⟨a, ?_⟩
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change (Real.sqrt L : ℂ) • F = z.fst
    simp only [F, smul_smul, mul_inv_cancel₀ hc, one_smul]
  · exact hquot

/-- Completeness holds for every real graph index, in particular the entire fractional Sobolev range. -/
instance : CompleteSpace (IntrinsicIntervalSobolev s L) :=
  (completeSpace_iff_isComplete_range graphIsometry.isometry.isUniformInducing).mpr
    isClosed_range_graph.isComplete

/-- The exact intrinsic norm is induced by the physical graph inner product. -/
instance : InnerProductSpace ℂ (IntrinsicIntervalSobolev s L) := InnerProductSpace.induced graph

/-- The graph identification preserves inner products as well as norms. -/
theorem inner_eq_graph (f g : IntrinsicIntervalSobolev s L) :
    inner ℂ f g = inner ℂ (graph f) (graph g) := rfl

/-- The physical inner product keeps the interval length and both graph components. -/
theorem inner_eq (f g : IntrinsicIntervalSobolev s L) :
    inner ℂ f g = (L : ℂ) * inner ℂ f.val g.val + inner ℂ (quotient f) (quotient g) := by
  rw [inner_eq_graph]
  change inner ℂ ((Real.sqrt L : ℂ) • f.val) ((Real.sqrt L : ℂ) • g.val) +
    inner ℂ (quotient f) (quotient g) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  simp only [Complex.conj_ofReal, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt (Fact.out : 0 < L))]

/-- Intrinsic convergence is exactly simultaneous convergence of the two physical graph components. -/
theorem tendsto_iff_components {ι : Type*} {l : Filter ι}
    {f : ι → IntrinsicIntervalSobolev s L} {F : IntrinsicIntervalSobolev s L} :
    Tendsto f l (𝓝 F) ↔
      Tendsto (fun i => (f i).val) l (𝓝 F.val) ∧ Tendsto (fun i => quotient (f i)) l (𝓝 (quotient F)) := by
  constructor
  · intro h
    exact ⟨toL2Continuous.continuous.tendsto F |>.comp h,
      quotientContinuous.continuous.tendsto F |>.comp h⟩
  · rintro ⟨hf, hg⟩
    apply graphIsometry.isometry.tendsto_nhds_iff.mpr
    have hp : Tendsto (fun i => ((Real.sqrt L : ℂ) • (f i).val, quotient (f i))) l
        (𝓝 ((Real.sqrt L : ℂ) • F.val, quotient F)) :=
      (tendsto_const_nhds.smul hf).prodMk_nhds hg
    exact (WithLp.homeomorphProd 2 CircleL2 (Lp ℂ 2 (intervalProductMeasure L))).symm.continuous.tendsto _ |>.comp hp

/-- Limits of intrinsic Cauchy sequences exist in the same physical space. -/
theorem exists_limit_of_cauchy {f : ℕ → IntrinsicIntervalSobolev s L} (hf : CauchySeq f) :
    ∃ F : IntrinsicIntervalSobolev s L, Tendsto f atTop (𝓝 F) := cauchySeq_tendsto_of_complete hf

end NLS.Fourier.IntrinsicIntervalSobolev
