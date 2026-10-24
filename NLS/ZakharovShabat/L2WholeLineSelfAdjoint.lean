import NLS.ZakharovShabat.L2WholeLineSymmetry
import NLS.ZakharovShabat.L2WholeLineMaximalDomain
import NLS.ZakharovShabat.L2WholeLineAdjointSymmetry
import NLS.FunctionalAnalysis.SymmetricAdjoint
import NLS.FunctionalAnalysis.DoubleAdjointClosure

/-! # The self-adjoint real whole-line physical operator

The actual Hilbert adjoint equals the graph closure of the original smooth
compact test operator. Its maximal differential domain consists exactly of
L2 classes with locally AC representatives and L2 physical images.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual adjoint contains the dense original smooth compact test domain. -/
theorem wholeLineMinimalOperator_adjoint_dense_domain
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    Dense ((wholeLineMinimalOperator u).adjoint.domain : Set WholeLineL2) :=
  (wholeLineMinimalOperator_dense_domain u).mono (wholeLineMinimalOperator_le_adjoint u hu).1

/-- The actual maximal physical operator is self-adjoint. -/
theorem wholeLineMinimalOperator_adjoint_isSelfAdjoint
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    IsSelfAdjoint (wholeLineMinimalOperator u).adjoint :=
  isSelfAdjoint_adjoint_of_symmetric_adjoint (wholeLineMinimalOperator_dense_domain u)
    (wholeLineMinimalOperator_isFormalAdjoint u hu)
    (wholeLineMinimalOperator_adjoint_isFormalAdjoint u hu)

/-- The original minimal operator is essentially self-adjoint: its actual
graph closure equals its actual Hilbert-space adjoint. -/
theorem wholeLineMinimalOperator_closure_eq_adjoint
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).closure = (wholeLineMinimalOperator u).adjoint :=
  (adjoint_adjoint_eq_closure (wholeLineMinimalOperator_dense_domain u)
    (wholeLineMinimalOperator_adjoint_dense_domain u hu)
    (wholeLineMinimalOperator_isClosable u hu)).symm.trans
      (LinearPMap.isSelfAdjoint_def.mp (wholeLineMinimalOperator_adjoint_isSelfAdjoint u hu))

/-- Self-adjointness of the graph closure uses Mathlib's actual adjoint. -/
theorem wholeLineMinimalOperator_closure_isSelfAdjoint
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    IsSelfAdjoint (wholeLineMinimalOperator u).closure := by
  rw [wholeLineMinimalOperator_closure_eq_adjoint u hu]
  exact wholeLineMinimalOperator_adjoint_isSelfAdjoint u hu

/-- The self-adjoint graph closure has the original maximal differential domain. -/
theorem mem_wholeLineMinimalOperator_closure_domain_iff_AC
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) (f : WholeLineL2) :
    f ∈ (wholeLineMinimalOperator u).closure.domain ↔
      ∃ (F : ℝ → ℂ × ℂ) (g : WholeLineL2), wholeLineL2Pair f =ᵐ[volume] F ∧
        (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
        physicalOperator (l2WholeLinePotential u) F =ᵐ[volume] wholeLineL2Pair g := by
  rw [wholeLineMinimalOperator_closure_eq_adjoint u hu]
  exact mem_wholeLineMinimalOperator_adjoint_domain_iff_AC u hu f

/-- The original compact smooth test domain is a core for the maximal
self-adjoint physical operator. -/
theorem wholeLineMinimalOperator_adjoint_test_core
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).adjoint.HasCore (wholeLineMinimalOperator u).domain := by
  rw [← wholeLineMinimalOperator_closure_eq_adjoint u hu]
  exact wholeLineMinimalOperator_test_core u

/-- Essential self-adjointness applies to the unchanged original real Hilbert source. -/
theorem source_wholeLineMinimalOperator_closure_isSelfAdjoint
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsSelfAdjoint (wholeLineMinimalOperator (sourcePhysicalL2 φ)).closure :=
  wholeLineMinimalOperator_closure_isSelfAdjoint _ ((sourcePhysicalL2_realType_iff φ).mpr hφ)

end NLS.ZakharovShabat
