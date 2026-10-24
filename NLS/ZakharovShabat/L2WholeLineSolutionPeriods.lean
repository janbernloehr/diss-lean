import NLS.ZakharovShabat.L2WholeLineFundamental
import NLS.ZakharovShabat.L2FundamentalInitialValue

/-! # The original physical L2 equation on every integer period

The all-real-time continuation agrees on each closed period with the
actual unit-interval solution having its transported initial value.
The original signed differential equation therefore holds almost
everywhere in the local coordinate of each positive or negative period.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The fundamental matrix acts on arbitrary initial vectors by the
already constructed physical L2 initial-value solution. -/
theorem l2FundamentalMatrix_mulVec_eq_solutionPair
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (t : Icc (0 : ℝ) 1) :
    ((l2FundamentalMatrix u z t *ᵥ v) 0,(l2FundamentalMatrix u z t *ᵥ v) 1) =
      l2SolutionCurve u z (v 0,v 1) t := by
  rw [l2SolutionCurve_linearCombination]
  apply Prod.ext <;>
    simp [l2FundamentalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,smul_eq_mul] <;> ring

/-- The all-real-time physical pair propagated from an arbitrary initial vector. -/
def l2WholeLineSolution (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (t : ℝ) : ℂ × ℂ :=
  ((l2WholeLineFundamentalMatrix u z t *ᵥ v) 0,
    (l2WholeLineFundamentalMatrix u z t *ᵥ v) 1)

@[simp] theorem l2WholeLineSolution_zero (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    l2WholeLineSolution u z v 0 = (v 0,v 1) := by
  simp [l2WholeLineSolution]

/-- On any closed integer period the continuation is the actual L2
solution with its monodromy-transported initial vector. -/
theorem l2WholeLineSolution_on_period (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (n : ℤ) (s : Icc (0 : ℝ) 1) :
    l2WholeLineSolution u z v (s.val+n) =
      l2SolutionCurve u z
        (((↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) 0,
         ((↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) 1) s := by
  have ht : s.val+(n : ℝ) ∈ Icc (n : ℝ) ((n : ℝ)+1) := by
    constructor <;> linarith [s.property.1,s.property.2]
  unfold l2WholeLineSolution
  rw [l2WholeLineFundamentalMatrix_on_period u z n _ ht]
  have he : (⟨s.val+(n : ℝ)-n,by constructor <;> linarith [ht.1,ht.2]⟩ : Icc (0 : ℝ) 1) = s := by
    apply Subtype.ext
    simp
  rw [he,← Matrix.mulVec_mulVec]
  exact l2FundamentalMatrix_mulVec_eq_solutionPair u z _ s

/-- Around each interior point of any period, the actual continuation
equals the translated unit-interval solution on a whole neighborhood. -/
theorem l2WholeLineSolution_eventuallyEq_period
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (n : ℤ)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    (fun t : ℝ => l2WholeLineSolution u z v (t+n)) =ᶠ[𝓝 s]
      extend (l2SolutionCurve u z
        (((↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) 0,
         ((↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) 1)) := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht'] using
    l2WholeLineSolution_on_period u z v n ⟨t,ht'⟩

/-- The original signed first-order system holds almost everywhere on
each integer period, expressed in its local unit-interval coordinate. -/
theorem ae_hasDerivAt_l2WholeLineSolution_period
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (n : ℤ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun t : ℝ => l2WholeLineSolution u z v (t+n))
        (classicalODECoefficient (intervalL2Representative u s) z
          (l2WholeLineSolution u z v (s+n))) s := by
  let w : Fin 2 → ℂ := (↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
  have hne : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), s ≠ (1 : ℝ) :=
    ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_hasDerivAt_l2SolutionCurve u z (w 0,w 1),hne] with s hs hd hn
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1,lt_of_le_of_ne hs.2 hn⟩
  have he := l2WholeLineSolution_eventuallyEq_period u z v n s hs'
  have hval := he.eq_of_nhds
  rw [hval]
  exact hd.congr_of_eventuallyEq he

end NLS.ZakharovShabat
