import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.CoefficientDecay

/-!
# Deleting a distant coordinate

At a fixed `ℓᵖ` sequence with finite exponent, one coordinate tends
to zero as its index escapes in either direction. Hence the
deleted-coordinate projections converge strongly to the identity.
This is used when comparing the selected psi data to the full root
sequence in Lemma 12.10.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Deleting one coordinate changes the norm by exactly the norm of
that coordinate. -/
theorem norm_deleteCoordinate_sub (n : ℤ) (a : Coeff p) :
    ‖deleteCoordinate n a - a‖ = ‖a n‖ := by
  have hdiff : deleteCoordinate n a - a =
      -(lp.single p n (a n) : Coeff p) := by
    change (a - lp.single p n (a n)) - a = _
    abel
  rw [hdiff,norm_neg]
  simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]

/-- The deleted-coordinate projections tend strongly to the identity
as the deleted index tends to either end of `ℤ`. -/
theorem tendsto_deleteCoordinate_at_natAbs
    (hp : p ≠ ⊤) (a : Coeff p) :
    Tendsto (fun n : ℤ => deleteCoordinate n a)
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := exists_cutoff_norm_apply_lt hp a hε
  apply eventually_comap.mpr
  apply eventually_atTop.mpr
  refine ⟨K,?_⟩
  intro j hj n hn
  rw [dist_eq_norm,norm_deleteCoordinate_sub]
  exact hK n (hn ▸ hj)

end NLS.Coeff
