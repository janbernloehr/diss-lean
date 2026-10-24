import NLS.ZakharovShabat.L2WholeLineOfPair
import NLS.ZakharovShabat.L2WholeLineSelfAdjoint
import NLS.ZakharovShabat.PhysicalOperatorProductRule

/-! # Compact cutoffs of actual whole-line physical solutions

The cutoff belongs to the actual maximal differential domain. Its spectral
residual is exactly the signed cutoff derivative, with no smoothness
assumption on the periodic L2 potential.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The residual for the pencil z-L caused by a scalar cutoff. -/
def physicalCutoffResidual (ψ : ℝ → ℂ) (F : ℝ → ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  (-I * deriv ψ t * (F t).1,I * deriv ψ t * (F t).2)

theorem memLp_physicalCutoffResidual (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (F : ℝ → ℂ × ℂ) (hF : Continuous F) :
    MemLp (physicalCutoffResidual ψ F) 2 volume := by
  have hcont : Continuous (physicalCutoffResidual ψ F) :=
    ((hψ.continuous_deriv_one.const_mul (-I)).mul hF.fst).prodMk
      ((hψ.continuous_deriv_one.const_mul I).mul hF.snd)
  have hcomp : HasCompactSupport (physicalCutoffResidual ψ F) := by
    apply HasCompactSupport.of_support_subset_isCompact hc.deriv
    intro t ht
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact ht (by simp [physicalCutoffResidual,hz])
  exact hcont.memLp_of_hasCompactSupport hcomp

theorem memLp_wholeLineCutoffPair (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    MemLp (fun t => ψ t • l2WholeLineSolution u z v t) 2 volume :=
  (hψ.smul (continuous_l2WholeLineSolution u z v)).memLp_of_hasCompactSupport hc.smul_right

/-- Multiplication of the physical solution produces the exact original
differential image, almost everywhere on the whole line. -/
theorem ae_physicalOperator_wholeLineCutoff (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) :
    physicalOperator (l2WholeLinePotential u) (fun t => ψ t • l2WholeLineSolution u z v t)
      =ᵐ[volume] (fun t => z • (ψ t • l2WholeLineSolution u z v t) -
        physicalCutoffResidual ψ (l2WholeLineSolution u z v) t) := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z v,
    ae_physicalOperator_l2WholeLineSolution u z v] with t hd he
  rw [physicalOperator_smul_of_differentiableAt _ _ ψ t
    (hψ.differentiable one_ne_zero t) hd.differentiableAt,he]
  apply Prod.ext <;> simp [physicalCutoffResidual,smul_eq_mul] <;> ring

/-- The cutoff defines an element of the original whole-line Hilbert space. -/
def wholeLineCutoff (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : WholeLineL2 :=
  wholeLineOfPair _ (memLp_wholeLineCutoffPair u z v ψ hψ hc)

/-- Its original differential image is square integrable by the exact
product equation, although the physical solution need only be locally AC. -/
theorem memLp_wholeLineCutoffImage (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    MemLp (fun t => z • (ψ t • l2WholeLineSolution u z v t) -
      physicalCutoffResidual ψ (l2WholeLineSolution u z v) t) 2 volume :=
  ((memLp_wholeLineCutoffPair u z v ψ hψ.continuous hc).const_smul z).sub
    (memLp_physicalCutoffResidual ψ hψ hc _ (continuous_l2WholeLineSolution u z v))

/-- Every smooth compact cutoff lies in the actual self-adjoint closure domain. -/
theorem wholeLineCutoff_mem_closure_domain (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    wholeLineCutoff u z v ψ hψ.continuous hc ∈ (wholeLineMinimalOperator u).closure.domain := by
  apply (mem_wholeLineMinimalOperator_closure_domain_iff_AC u hu _).mpr
  let G := fun t => z • (ψ t • l2WholeLineSolution u z v t) -
    physicalCutoffResidual ψ (l2WholeLineSolution u z v) t
  have hG : MemLp G 2 volume := memLp_wholeLineCutoffImage u z v ψ hψ hc
  refine ⟨fun t => ψ t • l2WholeLineSolution u z v t,wholeLineOfPair G hG,
    wholeLineL2Pair_ofPair_ae _ _,?_,?_⟩
  · intro a b
    exact hψ.contDiffOn.absolutelyContinuousOnInterval.smul
      (absolutelyContinuousOnInterval_l2WholeLineSolution u z v a b)
  · exact (ae_physicalOperator_wholeLineCutoff u z v ψ hψ).trans
      (wholeLineL2Pair_ofPair_ae G hG).symm

/-- The actual graph-closure operator has exactly the differential image
computed by the cutoff product equation. -/
theorem wholeLineCutoff_closure_apply (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (wholeLineMinimalOperator u).closure
      ⟨wholeLineCutoff u z v ψ hψ.continuous hc,wholeLineCutoff_mem_closure_domain u hu z v ψ hψ hc⟩ =
      wholeLineOfPair (fun t => z • (ψ t • l2WholeLineSolution u z v t) -
        physicalCutoffResidual ψ (l2WholeLineSolution u z v) t)
        (memLp_wholeLineCutoffImage u z v ψ hψ hc) := by
  let F := fun t => ψ t • l2WholeLineSolution u z v t
  let G := fun t => z • (ψ t • l2WholeLineSolution u z v t) -
    physicalCutoffResidual ψ (l2WholeLineSolution u z v) t
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b :=
    hψ.contDiffOn.absolutelyContinuousOnInterval.smul
      (absolutelyContinuousOnInterval_l2WholeLineSolution u z v a b)
  have hp : physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
      wholeLineL2Pair (wholeLineOfPair G (memLp_wholeLineCutoffImage u z v ψ hψ hc)) :=
    (ae_physicalOperator_wholeLineCutoff u z v ψ hψ).trans (wholeLineL2Pair_ofPair_ae G _).symm
  have hw := wholeLineWeakEquation_of_AC_representative u hu
    (wholeLineCutoff u z v ψ hψ.continuous hc)
    (wholeLineOfPair G (memLp_wholeLineCutoffImage u z v ψ hψ hc))
    F (wholeLineL2Pair_ofPair_ae F _) hac hp
  have he := (le_of_eq (wholeLineMinimalOperator_closure_eq_adjoint u hu)).2
    (show ((⟨wholeLineCutoff u z v ψ hψ.continuous hc,
      wholeLineCutoff_mem_closure_domain u hu z v ψ hψ hc⟩ :
        (wholeLineMinimalOperator u).closure.domain) : WholeLineL2) =
      ((⟨wholeLineCutoff u z v ψ hψ.continuous hc,hw.mem_adjoint_domain⟩ :
        (wholeLineMinimalOperator u).adjoint.domain) : WholeLineL2) from rfl)
  exact he.trans hw.adjoint_eq

end NLS.ZakharovShabat
