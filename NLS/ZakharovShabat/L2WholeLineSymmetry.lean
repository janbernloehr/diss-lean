import NLS.ZakharovShabat.L2WholeLineMinimalOperator
import NLS.ZakharovShabat.L2WholeLineReality
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Symmetry of the actual minimal whole-line operator

Compact support removes the boundary terms in the original signed physical
expression. Real physical potentials give symmetry in the Hermitian L2
inner product and containment in Mathlib's actual adjoint. Equality with
the adjoint, and hence self-adjointness, is not asserted.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- The integral of the derivative of a compactly supported C1 scalar
test vanishes on the whole real line. -/
theorem integral_deriv_compact_test {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∫ t : ℝ, deriv f t = 0 := by
  have hi : Integrable (deriv f) volume :=
    hf.continuous_deriv_one.integrable_of_hasCompactSupport hfc.deriv
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi,compl_Iic,
    HasCompactSupport.integral_Iic_deriv_eq hf hfc,
    HasCompactSupport.integral_Ioi_deriv_eq hf hfc,add_neg_cancel]



/-- The actual minimal test operator satisfies the Hermitian pairing
identity whenever the original physical potential is real type. -/
theorem inner_wholeLineTestOperator_symmetric (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (f g : WholeLineTestFunction) :
    inner ℂ (wholeLineTestOperator u f) (wholeLineTestInclusion g) =
      inner ℂ (wholeLineTestInclusion f) (wholeLineTestOperator u g) := by
  have hF : ContDiff ℝ 1 (fun t => (f t).ofLp) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).contDiff.comp (f.property.1.of_le (by norm_num))
  have hG : ContDiff ℝ 1 (fun t => (g t).ofLp) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).contDiff.comp (g.property.1.of_le (by norm_num))
  let B : ℝ → ℂ := fun t =>
    -Complex.I * star (f t).ofLp.1 * (g t).ofLp.1 +
      Complex.I * star (f t).ofLp.2 * (g t).ofLp.2
  have hB : ContDiff ℝ 1 B :=
    (((Complex.conjCLE.contDiff.comp hF.fst).const_smul (-Complex.I)).mul hG.fst).add
      (((Complex.conjCLE.contDiff.comp hF.snd).const_smul Complex.I).mul hG.snd)
  have hfc1 : HasCompactSupport (fun t => star (f t).ofLp.1) :=
    f.property.2.comp_left (g := fun v : WholeLineVector => star v.ofLp.1) (by simp)
  have hfc2 : HasCompactSupport (fun t => star (f t).ofLp.2) :=
    f.property.2.comp_left (g := fun v : WholeLineVector => star v.ofLp.2) (by simp)
  have hBc : HasCompactSupport B :=
    (hfc1.mul_left.mul_right).add (hfc2.mul_left.mul_right)
  rw [L2.inner_def,L2.inner_def]
  apply sub_eq_zero.mp
  rw [← integral_sub (L2.integrable_inner (wholeLineTestOperator u f) (wholeLineTestInclusion g))
    (L2.integrable_inner (wholeLineTestInclusion f) (wholeLineTestOperator u g))]
  have he : (fun t => inner ℂ (wholeLineTestOperator u f t) (wholeLineTestInclusion g t) -
      inner ℂ (wholeLineTestInclusion f t) (wholeLineTestOperator u g t)) =ᵐ[volume] deriv B := by
    filter_upwards [wholeLineTestOperator_ae u f,wholeLineTestOperator_ae u g,
      wholeLineTestInclusion_ae f,wholeLineTestInclusion_ae g,ae_l2WholeLinePotential_real u hu]
      with t hof hog hif hig hr
    rw [hof,hog,hif,hig]
    have hd := (((hF.fst.differentiable one_ne_zero t).hasDerivAt.star.const_mul (-Complex.I)).mul
      (hG.fst.differentiable one_ne_zero t).hasDerivAt).add
      (((hF.snd.differentiable one_ne_zero t).hasDerivAt.star.const_mul Complex.I).mul
        (hG.snd.differentiable one_ne_zero t).hasDerivAt)
    have hd' : HasDerivAt B
        (-Complex.I * star (deriv (fun x => (f x).ofLp.1) t) * (g t).ofLp.1 +
          -Complex.I * star (f t).ofLp.1 * deriv (fun x => (g x).ofLp.1) t +
        (Complex.I * star (deriv (fun x => (f x).ofLp.2) t) * (g t).ofLp.2 +
          Complex.I * star (f t).ofLp.2 * deriv (fun x => (g x).ofLp.2) t)) t := by
      convert! hd using 1
    rw [hd'.deriv]
    simp only [wholeLineTestPhysicalExpression,physicalOperator,WithLp.prod_inner_apply,
      RCLike.inner_apply']
    rw [hr]
    simp
    ring
  rw [integral_congr_ae he]
  exact integral_deriv_compact_test hB hBc

/-- Symmetry is expressed using Mathlib's actual formal-adjoint relation
on the densely defined partial operator. -/
theorem wholeLineMinimalOperator_isFormalAdjoint (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).IsFormalAdjoint (wholeLineMinimalOperator u) := by
  intro x y
  obtain ⟨f,rfl⟩ := wholeLineTestDomainEquiv.surjective x
  obtain ⟨g,rfl⟩ := wholeLineTestDomainEquiv.surjective y
  rw [wholeLineMinimalOperator_test,wholeLineMinimalOperator_test]
  exact inner_wholeLineTestOperator_symmetric u hu f g

/-- The real minimal operator is contained in its actual Hilbert-space adjoint. -/
theorem wholeLineMinimalOperator_le_adjoint (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    wholeLineMinimalOperator u ≤ (wholeLineMinimalOperator u).adjoint :=
  (wholeLineMinimalOperator_isFormalAdjoint u hu).le_adjoint
    (wholeLineMinimalOperator_dense_domain u)

/-- The actual adjoint of the dense minimal operator is closed. -/
theorem wholeLineMinimalOperator_adjoint_isClosed (u : IntervalPairL2) :
    (wholeLineMinimalOperator u).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (wholeLineMinimalOperator_dense_domain u)


/-- Real physical potentials give a closable minimal operator, using
its closed Hilbert-space adjoint as an actual extension. -/
theorem wholeLineMinimalOperator_isClosable (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).IsClosable :=
  (wholeLineMinimalOperator_adjoint_isClosed u).isClosable.leIsClosable
    (wholeLineMinimalOperator_le_adjoint u hu)

/-- The graph closure is a closed operator for every real physical potential. -/
theorem wholeLineMinimalOperator_closure_isClosed (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).closure.IsClosed :=
  (wholeLineMinimalOperator_isClosable u hu).closure_isClosed

/-- The closure retains a dense domain. -/
theorem wholeLineMinimalOperator_closure_dense_domain (u : IntervalPairL2) :
    Dense (↑(wholeLineMinimalOperator u).closure.domain : Set WholeLineL2) :=
  (wholeLineMinimalOperator_dense_domain u).mono (wholeLineMinimalOperator u).le_closure.1

/-- The original compact smooth test domain is a core for the graph closure. -/
theorem wholeLineMinimalOperator_test_core (u : IntervalPairL2) :
    (wholeLineMinimalOperator u).closure.HasCore (wholeLineMinimalOperator u).domain :=
  (wholeLineMinimalOperator u).closureHasCore

/-- Closability applies to the unchanged original real Hilbert sources. -/
theorem source_wholeLineMinimalOperator_isClosable (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    (wholeLineMinimalOperator (sourcePhysicalL2 φ)).IsClosable :=
  wholeLineMinimalOperator_isClosable _ ((sourcePhysicalL2_realType_iff φ).mpr hφ)

end NLS.ZakharovShabat
