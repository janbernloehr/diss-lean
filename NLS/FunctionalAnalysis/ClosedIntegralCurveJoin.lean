import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-! # Joining integral curves on adjacent closed intervals

For a time-dependent field, matching values and within-interval derivatives
at the common endpoint give a solution on the entire joined interval.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*}

/-- A closed-interval join, assigning the common endpoint to the first curve. -/
def joinClosedCurves (c : ℝ) (f g : ℝ → E) (time : ℝ) : E :=
  if time ≤ c then f time else g time

@[simp] theorem joinClosedCurves_of_le (c : ℝ) (f g : ℝ → E) {time : ℝ} (ht : time ≤ c) :
    joinClosedCurves c f g time = f time := by simp [joinClosedCurves,ht]

theorem joinClosedCurves_of_ge (c : ℝ) (f g : ℝ → E) (he : f c = g c)
    {time : ℝ} (ht : c ≤ time) : joinClosedCurves c f g time = g time := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa [joinClosedCurves] using he
  · simp [joinClosedCurves,ht.not_ge]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adjacent closed-interval solutions glue, including the derivative at the join. -/
theorem hasDerivWithinAt_joinClosedCurves
    (F : ℝ → E → E) (f g : ℝ → E) (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ r ∈ Icc a c, HasDerivWithinAt f (F r (f r)) (Icc a c) r)
    (hg : ∀ r ∈ Icc c b, HasDerivWithinAt g (F r (g r)) (Icc c b) r)
    (he : f c = g c) :
    ∀ r ∈ Icc a b, HasDerivWithinAt (joinClosedCurves c f g)
      (F r (joinClosedCurves c f g r)) (Icc a b) r := by
  let j := joinClosedCurves c f g
  have hl (r : ℝ) (hr : r ∈ Icc a c) : HasDerivWithinAt j (F r (j r)) (Icc a c) r := by
    have hj : ∀ x ∈ Icc a c, j x = f x := fun x hx => joinClosedCurves_of_le c f g hx.2
    rw [hj r hr]
    exact (hf r hr).congr_of_mem hj hr
  have hr (r : ℝ) (hr : r ∈ Icc c b) : HasDerivWithinAt j (F r (j r)) (Icc c b) r := by
    have hj : ∀ x ∈ Icc c b, j x = g x := fun x hx => joinClosedCurves_of_ge c f g he hx.1
    rw [hj r hr]
    exact (hg r hr).congr_of_mem hj hr
  intro r h
  rcases lt_trichotomy r c with hrc | heq | hcr
  · apply (hl r ⟨h.1,hrc.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hrc)] with x hx hxc
    exact ⟨hx.1,hxc.le⟩
  · subst r
    have hd := (hl c ⟨hac,le_rfl⟩).union (hr c ⟨le_rfl,hcb⟩)
    rwa [Icc_union_Icc_eq_Icc hac hcb] at hd
  · apply (hr r ⟨hcr.le,h.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcr)] with x hx hcx
    exact ⟨hcx.le,hx.2⟩

end NLS.FunctionalAnalysis
