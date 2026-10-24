import NLS.ZakharovShabat.L2WholeLineMinimalOperator
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # The actual adjoint characterized by the weak physical equation

The equation uses the original differential expression on compact smooth
tests and the unchanged L2 representatives. Both implications refer to
Mathlib's Hilbert-space adjoint of the actual dense minimal operator.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- The original physical equation in weak form on the whole real line. -/
def WholeLineWeakEquation (u : IntervalPairL2) (f g : WholeLineL2) : Prop :=
  ∀ h : WholeLineTestFunction,
    (∫ t : ℝ, inner ℂ (wholeLineTestPhysicalExpression u h t) (f t)) =
      ∫ t : ℝ, inner ℂ (h t) (g t)

theorem wholeLineWeakEquation_iff_test_pairing (u : IntervalPairL2) (f g : WholeLineL2) :
    WholeLineWeakEquation u f g ↔ ∀ h : WholeLineTestFunction,
      inner ℂ (wholeLineTestOperator u h) f = inner ℂ (wholeLineTestInclusion h) g := by
  have hleft (h : WholeLineTestFunction) :
      inner ℂ (wholeLineTestOperator u h) f =
        ∫ t : ℝ, inner ℂ (wholeLineTestPhysicalExpression u h t) (f t) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [wholeLineTestOperator_ae u h] with t ht
    rw [ht]
  have hright (h : WholeLineTestFunction) :
      inner ℂ (wholeLineTestInclusion h) g = ∫ t : ℝ, inner ℂ (h t) (g t) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [wholeLineTestInclusion_ae h] with t ht
    rw [ht]
  simp only [WholeLineWeakEquation,hleft,hright]

/-- The weak residual has zero integral, with integrability justified by
the actual L2 test inclusion and physical operator image. -/
theorem WholeLineWeakEquation.integral_residual_eq_zero
    {u : IntervalPairL2} {f g : WholeLineL2} (hfg : WholeLineWeakEquation u f g)
    (h : WholeLineTestFunction) :
    (∫ t : ℝ, inner ℂ (wholeLineTestPhysicalExpression u h t) (f t) -
      inner ℂ (h t) (g t)) = 0 := by
  have hi : Integrable (fun t => inner ℂ (wholeLineTestPhysicalExpression u h t) (f t)) volume := by
    apply (L2.integrable_inner (wholeLineTestOperator u h) f).congr
    filter_upwards [wholeLineTestOperator_ae u h] with t ht
    rw [ht]
  have hj : Integrable (fun t => inner ℂ (h t) (g t)) volume := by
    apply (L2.integrable_inner (wholeLineTestInclusion h) g).congr
    filter_upwards [wholeLineTestInclusion_ae h] with t ht
    rw [ht]
  rw [integral_sub hi hj,hfg h,sub_self]

/-- Every element of the actual adjoint domain satisfies the original
weak physical equation with its actual adjoint image. -/
theorem wholeLineMinimalOperator_adjoint_weakEquation (u : IntervalPairL2)
    (f : (wholeLineMinimalOperator u).adjoint.domain) :
    WholeLineWeakEquation u f ((wholeLineMinimalOperator u).adjoint f) := by
  rw [wholeLineWeakEquation_iff_test_pairing]
  intro h
  have he := (LinearPMap.adjoint_isFormalAdjoint (wholeLineMinimalOperator_dense_domain u)).symm
    (wholeLineTestDomainEquiv h) f
  rw [wholeLineMinimalOperator_test] at he
  simpa only [wholeLineTestDomainEquiv,LinearEquiv.ofInjective_apply] using! he

/-- Conversely, an L2 solution of the weak physical equation belongs
to the actual adjoint domain, and its proposed image is the adjoint image. -/
theorem WholeLineWeakEquation.mem_adjoint_domain {u : IntervalPairL2} {f g : WholeLineL2}
    (hfg : WholeLineWeakEquation u f g) :
    f ∈ (wholeLineMinimalOperator u).adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists f
  refine ⟨g,?_⟩
  intro h
  obtain ⟨q,rfl⟩ := wholeLineTestDomainEquiv.surjective h
  have he := (wholeLineWeakEquation_iff_test_pairing u f g).mp hfg q
  rw [wholeLineMinimalOperator_test]
  rw [← inner_conj_symm,← inner_conj_symm f,he]
  rfl

theorem WholeLineWeakEquation.adjoint_eq {u : IntervalPairL2} {f g : WholeLineL2}
    (hfg : WholeLineWeakEquation u f g) :
    (wholeLineMinimalOperator u).adjoint ⟨f,hfg.mem_adjoint_domain⟩ = g := by
  apply LinearPMap.adjoint_apply_eq (wholeLineMinimalOperator_dense_domain u)
  intro h
  obtain ⟨q,rfl⟩ := wholeLineTestDomainEquiv.surjective h
  have he := (wholeLineWeakEquation_iff_test_pairing u f g).mp hfg q
  rw [wholeLineMinimalOperator_test]
  rw [← inner_conj_symm,← inner_conj_symm f,he]
  rfl

/-- The full adjoint domain consists exactly of L2 vectors with an L2
image for the original weak physical equation. -/
theorem mem_wholeLineMinimalOperator_adjoint_domain_iff (u : IntervalPairL2) (f : WholeLineL2) :
    f ∈ (wholeLineMinimalOperator u).adjoint.domain ↔ ∃ g : WholeLineL2, WholeLineWeakEquation u f g := by
  constructor
  · intro hf
    exact ⟨_,wholeLineMinimalOperator_adjoint_weakEquation u ⟨f,hf⟩⟩
  · rintro ⟨g,hg⟩
    exact hg.mem_adjoint_domain

end NLS.ZakharovShabat
