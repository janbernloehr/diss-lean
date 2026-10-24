import NLS.ZakharovShabat.L2WholeLineTestOperator
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! # The whole-line Hilbert space and its dense compact test domain

The fibre carries the Hermitian Euclidean norm. Smooth compactly supported
pairs embed injectively into its whole-line L2 space and have dense range.
The physical differential expression has an L2 value on every such test.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The Hermitian two-component fibre of the whole-line spectral operator. -/
abbrev WholeLineVector := WithLp 2 (ℂ × ℂ)

/-- The physical Hilbert space on the real line with Lebesgue measure. -/
abbrev WholeLineL2 := Lp WholeLineVector 2 (volume : Measure ℝ)

/-- The submodule of smooth compactly supported pairs on the real line. -/
def wholeLineTestFunctions : Submodule ℂ (ℝ → WholeLineVector) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- Smooth compactly supported test pairs with their complex vector-space structure. -/
abbrev WholeLineTestFunction : Type := ↥wholeLineTestFunctions

instance : CoeFun WholeLineTestFunction (fun _ => ℝ → WholeLineVector) := ⟨Subtype.val⟩

theorem memLp_wholeLineTestFunction (f : WholeLineTestFunction) : MemLp f 2 volume :=
  f.property.1.continuous.memLp_of_hasCompactSupport f.property.2

/-- The canonical complex-linear inclusion of smooth compact tests into L2. -/
def wholeLineTestInclusion : WholeLineTestFunction →ₗ[ℂ] WholeLineL2 where
  toFun f := (memLp_wholeLineTestFunction f).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem wholeLineTestInclusion_ae (f : WholeLineTestFunction) :
    wholeLineTestInclusion f =ᵐ[volume] f :=
  (memLp_wholeLineTestFunction f).coeFn_toLp

/-- Continuity prevents distinct test functions from representing the same L2 class. -/
theorem wholeLineTestInclusion_injective : Function.Injective wholeLineTestInclusion := by
  intro f g h
  apply Subtype.ext
  apply Measure.eq_of_ae_eq (μ := (volume : Measure ℝ)) _ f.property.1.continuous g.property.1.continuous
  exact (wholeLineTestInclusion_ae f).symm.trans (h ▸ wholeLineTestInclusion_ae g)

/-- Smooth compactly supported pairs are dense in the actual Hermitian L2 space. -/
theorem denseRange_wholeLineTestInclusion : DenseRange wholeLineTestInclusion := by
  apply (Lp.dense_hasCompactSupport_contDiff (F := WholeLineVector) (μ := (volume : Measure ℝ))
    (p := 2) (by norm_num)).mono
  rintro f ⟨g,hfg,hgc,hgd⟩
  let t : WholeLineTestFunction := ⟨g,hgd,hgc⟩
  refine ⟨t,?_⟩
  apply Lp.ext
  exact (wholeLineTestInclusion_ae t).trans hfg.symm

/-- The unchanged signed physical differential expression, expressed in the Hermitian fibre. -/
def wholeLineTestPhysicalExpression (u : IntervalPairL2) (f : WholeLineTestFunction)
    (t : ℝ) : WholeLineVector :=
  WithLp.toLp 2 (physicalOperator (l2WholeLinePotential u) (fun s => (f s).ofLp) t)

/-- Each actual test-operator image belongs to the whole-line Hilbert space. -/
theorem memLp_wholeLineTestPhysicalExpression (u : IntervalPairL2) (f : WholeLineTestFunction) :
    MemLp (wholeLineTestPhysicalExpression u f) 2 volume := by
  have hfd : ContDiff ℝ 1 (fun s => (f s).ofLp) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).contDiff.comp (f.property.1.of_le (by norm_num))
  have hfc : HasCompactSupport (fun s => (f s).ofLp) := f.property.2.comp_left rfl
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp_memLp'
    (memLp_physicalOperator_l2WholeLine_test u hfd hfc)

end NLS.ZakharovShabat
