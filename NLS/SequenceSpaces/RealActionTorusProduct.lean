import NLS.SequenceSpaces.RealActionTorus
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

/-! # One circle for each nonzero action

Coordinate phases identify a based action torus with the product of unit
circles indexed by its nonzero actions. Compactness upgrades the continuous
bijection to a homeomorphism for every finite Banach sequence exponent.
The product may have infinitely many factors.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- The complex coordinate associated with a real action-coordinate pair. -/
def pairComplexCoordinate (z : RealCoeff p × RealCoeff p) (n : ℤ) : ℂ :=
  ⟨z.1 n,z.2 n⟩

theorem normSq_pairComplexCoordinate (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    Complex.normSq (pairComplexCoordinate z n) = 2*pairAction z n := by
  simp only [pairComplexCoordinate,Complex.normSq_apply,pairAction]
  ring

theorem pairComplexCoordinate_ne_zero (z : RealCoeff p × RealCoeff p) (n : ℤ)
    (hn : pairAction z n ≠ 0) : pairComplexCoordinate z n ≠ 0 := by
  intro h
  have he := normSq_pairComplexCoordinate z n
  rw [h,Complex.normSq_zero] at he
  exact hn (by linarith)

private theorem norm_pairComplexCoordinate_eq {z w : RealCoeff p × RealCoeff p}
    {n : ℤ} (h : pairAction z n = pairAction w n) :
    ‖pairComplexCoordinate z n‖ = ‖pairComplexCoordinate w n‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm,Complex.sq_norm,normSq_pairComplexCoordinate,
    normSq_pairComplexCoordinate,h]

/-- Relative phases at precisely the noncollapsed action coordinates. -/
def actionTorusPhases (z : RealCoeff p × RealCoeff p)
    (w : actionTorus p (pairAction z)) (n : {n : ℤ // pairAction z n ≠ 0}) : Circle :=
  ⟨pairComplexCoordinate w.val n.val / pairComplexCoordinate z n.val,by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,norm_pairComplexCoordinate_eq (w.property n.val)]
    exact div_self (norm_ne_zero_iff.mpr (pairComplexCoordinate_ne_zero z n.val n.property))⟩

/-- Relative phases determine every coordinate, with zero actions forcing the missing pairs to zero. -/
theorem actionTorusPhases_injective (z : RealCoeff p × RealCoeff p) :
    Function.Injective (actionTorusPhases z) := by
  intro x y h
  apply Subtype.ext
  have he (n : ℤ) : pairComplexCoordinate x.val n = pairComplexCoordinate y.val n := by
    by_cases hn : pairAction z n ≠ 0
    · have hc := congrArg (fun f => ((f ⟨n,hn⟩ : Circle) : ℂ)) h
      exact (div_left_inj' (pairComplexCoordinate_ne_zero z n hn)).mp hc
    · have hx := coordinates_zero_of_mem_actionTorus x.property n (not_ne_iff.mp hn)
      have hy := coordinates_zero_of_mem_actionTorus y.property n (not_ne_iff.mp hn)
      simp only [pairComplexCoordinate,hx.1,hx.2,hy.1,hy.2]
  apply Prod.ext <;> ext n
  · exact congrArg Complex.re (he n)
  · exact congrArg Complex.im (he n)

/-- Every selection of circle phases belongs to the original sequence space and realizes the actions. -/
theorem actionTorusPhases_surjective (z : RealCoeff p × RealCoeff p) :
    Function.Surjective (actionTorusPhases z) := by
  intro u
  let F : ℤ → ℂ := fun n => if hn : pairAction z n ≠ 0 then
    (u ⟨n,hn⟩ : ℂ)*pairComplexCoordinate z n else 0
  have hnorm (n : ℤ) : ‖F n‖ = ‖pairComplexCoordinate z n‖ := by
    by_cases hn : pairAction z n ≠ 0
    · simp only [F,dif_pos hn,norm_mul,Circle.norm_coe,one_mul]
    · have hz := coordinates_zero_of_mem_actionTorus (mem_actionTorus_self z) n (not_ne_iff.mp hn)
      simp only [F,dif_neg hn,pairComplexCoordinate,hz.1,hz.2]
      rfl
  have hm : Memℓp F p := ((lp.memℓp z.1).norm.add (lp.memℓp z.2).norm).mono (fun n => by
    rw [hnorm]
    exact Complex.norm_le_abs_re_add_abs_im _)
  let x : RealCoeff p := ⟨fun n => (F n).re,hm.mono' (fun n => Complex.abs_re_le_norm _)⟩
  let y : RealCoeff p := ⟨fun n => (F n).im,hm.mono' (fun n => Complex.abs_im_le_norm _)⟩
  have hc (n : ℤ) : pairComplexCoordinate (x,y) n = F n := by
    apply Complex.ext <;> rfl
  have ha : (x,y) ∈ actionTorus p (pairAction z) := by
    intro n
    have hs := congrArg (fun a : ℝ => a^2) (hnorm n)
    rw [← hc n,Complex.sq_norm,Complex.sq_norm,normSq_pairComplexCoordinate,
      normSq_pairComplexCoordinate] at hs
    linarith
  refine ⟨⟨(x,y),ha⟩,?_⟩
  funext n
  apply Circle.ext
  change pairComplexCoordinate (x,y) n.val / pairComplexCoordinate z n.val = (u n : ℂ)
  rw [hc]
  simp only [F,dif_pos n.property]
  exact mul_div_cancel_right₀ _ (pairComplexCoordinate_ne_zero z n.val n.property)

variable [Fact (1 ≤ p)]

/-- Coordinate phases are continuous from the sequence norm to the product topology. -/
theorem continuous_actionTorusPhases (z : RealCoeff p × RealCoeff p) :
    Continuous (actionTorusPhases z) := by
  apply continuous_pi
  intro n
  apply Continuous.subtype_mk
  have hx : Continuous (fun w : actionTorus p (pairAction z) => w.val.1 n.val) := ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n.val).continuous.comp continuous_fst).comp continuous_subtype_val
  have hy : Continuous (fun w : actionTorus p (pairAction z) => w.val.2 n.val) := ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n.val).continuous.comp continuous_snd).comp continuous_subtype_val
  simpa only [pairComplexCoordinate,Complex.mk_eq_add_mul_I,Function.comp_apply,
    Pi.add_apply,Pi.mul_apply] using
    ((Complex.continuous_ofReal.comp hx).add
      ((Complex.continuous_ofReal.comp hy).mul (continuous_const (y := Complex.I)))).div_const
        (pairComplexCoordinate z n.val)

/-- The norm-topological action torus is the product of one circle per nonzero action. -/
def actionTorusHomeomorphCircles (hp : p ≠ ⊤) (z : RealCoeff p × RealCoeff p) :
    actionTorus p (pairAction z) ≃ₜ ({n : ℤ // pairAction z n ≠ 0} → Circle) := by
  letI : CompactSpace (actionTorus p (pairAction z)) := isCompact_iff_compactSpace.mp (isCompact_actionTorus hp _)
  exact (Equiv.ofBijective (actionTorusPhases z)
    ⟨actionTorusPhases_injective z,actionTorusPhases_surjective z⟩).toHomeomorphOfContinuousClosed
      (continuous_actionTorusPhases z) (continuous_actionTorusPhases z).isClosedMap

end NLS.RealCoeff
