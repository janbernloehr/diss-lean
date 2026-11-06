import NLS.FunctionalAnalysis.CountableIntervalBox

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.FunctionalAnalysis



theorem intervalBox_projection_lift_fixed
    (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j) (N : ℕ)
    (f : countableIntervalBox l u → countableIntervalBox l u)
    (a : @NLS.CubicalSperner.unit_cube N)
    (hfix : intervalBoxFiniteProjection l u hle N (f (intervalBoxFiniteLift l u hle N a)) = a)
    (j : ℕ) (hj : j < N) :
    (f (intervalBoxFiniteLift l u hle N a)).val j = (intervalBoxFiniteLift l u hle N a).val j := by
  let x := f (intervalBoxFiniteLift l u hle N a)
  have hc := congrArg (fun b : @NLS.CubicalSperner.unit_cube N => b.val ⟨j,hj⟩) hfix
  change (if l j = u j then 0 else (x.val j-l j)/(u j-l j)) = a.val ⟨j,hj⟩ at hc
  change x.val j = (if h : j < N then l j+(u j-l j)*a.val ⟨j,h⟩ else l j)
  rw [dif_pos hj]
  by_cases hju : l j = u j
  · have hb := x.property j
    rw [← hju] at hb
    have hx : x.val j = l j := le_antisymm hb.2 hb.1
    rw [hx,← hju,sub_self,zero_mul,add_zero]
  · rw [if_neg hju] at hc
    have hw : u j-l j ≠ 0 := sub_ne_zero.mpr (Ne.symm hju)
    have he := (div_eq_iff hw).mp hc
    linarith

theorem exists_finite_coordinate_fixed_point
    (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j)
    (f : countableIntervalBox l u → countableIntervalBox l u) (hf : Continuous f) (N : ℕ) :
    ∃ x : countableIntervalBox l u, ∀ j : ℕ, j < N → (f x).val j = x.val j := by
  let F := fun a : @NLS.CubicalSperner.unit_cube N =>
    intervalBoxFiniteProjection l u hle N (f (intervalBoxFiniteLift l u hle N a))
  have hF : Continuous F := (continuous_intervalBoxFiniteProjection l u hle N).comp
    (hf.comp (continuous_intervalBoxFiniteLift l u hle N))
  obtain ⟨a,ha⟩ := NLS.CubicalSperner.fixed_point_unit_cube ⟨F,hF⟩
  exact ⟨intervalBoxFiniteLift l u hle N a,
    fun j hj => intervalBox_projection_lift_fixed l u hle N f a ha j hj⟩

end NLS.FunctionalAnalysis
