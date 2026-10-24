import NLS.ZakharovShabat.L2WholeLineSolutionPeriods
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Group.Measure

/-! # The physical L2 spectral equation almost everywhere on the real line

The unit-interval potential is extended by the fractional part of time.
Translation invariance and the countable set of integer seams assemble
the period equations into the actual differential equation on the line.
No whole-line unbounded operator or spectral measure is constructed here.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
namespace NLS.ZakharovShabat

/-- The period-one representative of an original physical unit-interval L2 potential. -/
def l2WholeLinePotential (u : IntervalPairL2) (t : ℝ) : ℂ × ℂ :=
  intervalL2Representative u (Int.fract t)

theorem l2WholeLinePotential_add_int (u : IntervalPairL2) (t : ℝ) (n : ℤ) :
    l2WholeLinePotential u (t+n) = l2WholeLinePotential u t := by
  simp [l2WholeLinePotential]

theorem periodic_l2WholeLinePotential (u : IntervalPairL2) :
    Function.Periodic (l2WholeLinePotential u) 1 := by
  intro t
  simpa using l2WholeLinePotential_add_int u t 1

/-- The original signed spectral equation holds almost everywhere on
the full real line with the actual periodically extended L2 potential. -/
theorem ae_hasDerivAt_l2WholeLineSolution
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    ∀ᵐ t : ℝ, HasDerivAt (l2WholeLineSolution u z v)
      (classicalODECoefficient (l2WholeLinePotential u t) z (l2WholeLineSolution u z v t)) t := by
  have hperiod (n : ℤ) : ∀ᵐ t : ℝ, t ∈ Ioo (n : ℝ) ((n : ℝ)+1) →
      HasDerivAt (l2WholeLineSolution u z v)
        (classicalODECoefficient (l2WholeLinePotential u t) z (l2WholeLineSolution u z v t)) t := by
    have h := ae_hasDerivAt_l2WholeLineSolution_period u z v n
    rw [ae_restrict_iff' measurableSet_Ioc] at h
    have hshift := (measurePreserving_sub_right volume (n : ℝ)).quasiMeasurePreserving.ae h
    filter_upwards [hshift] with t ht
    intro hmem
    have hs : t-(n : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hmem.1,hmem.2]
    have hd := (ht hs).comp_sub_const t (n : ℝ)
    have hf : ⌊t⌋ = n := Int.floor_eq_iff.mpr ⟨hmem.1.le,hmem.2⟩
    simpa only [sub_add_cancel,l2WholeLinePotential,Int.fract,hf] using hd
  have hall := ae_all_iff.mpr hperiod
  have hseam := (Set.countable_range (fun n : ℤ => (n : ℝ))).ae_notMem volume
  filter_upwards [hall,hseam] with t ht hnot
  have hne : t ≠ (⌊t⌋ : ℝ) := fun he => hnot ⟨⌊t⌋,he.symm⟩
  exact ht ⌊t⌋ ⟨lt_of_le_of_ne (Int.floor_le t) hne.symm,Int.lt_floor_add_one t⟩

/-- The literal physical differential expression equals the spectral
parameter times the same constructed solution, almost everywhere on R. -/
theorem ae_physicalOperator_l2WholeLineSolution
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    physicalOperator (l2WholeLinePotential u) (l2WholeLineSolution u z v)
      =ᵐ[volume] (fun t => z • l2WholeLineSolution u z v t) := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z v] with t ht
  simp only [physicalOperator,(HasFDerivAt.hasDerivAt ht.fst).deriv,
    (HasFDerivAt.hasDerivAt ht.snd).deriv,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

end NLS.ZakharovShabat
