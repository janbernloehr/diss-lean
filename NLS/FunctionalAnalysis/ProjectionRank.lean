import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Ring.Idempotent

/-!
# Rank stability of bounded projections

Two finite-rank projections at operator-norm distance less than one have equal
rank: each projection is injective on the range of the other. A nonzero
projection has norm at least one, so a continuous preconnected family cannot
deform zero into a nonzero projection. This also transports containment in
the range of a fixed commuting projection.
-/

noncomputable section

namespace NLS.ProjectionRank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A map within distance one of a projection is injective on its range. -/
theorem injective_on_range_of_norm_sub_lt_one (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hPQ : ‖P - Q‖ < 1) :
    Function.Injective (Q.toLinearMap.comp P.range.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hQ : Q x = 0 := hx
  have hPx : P x = x := by
    obtain ⟨y, hy⟩ := x.property
    change P y = (x : E) at hy
    have hi := congrArg (fun A : E →L[ℂ] E => A y) hP
    change P (P y) = P y at hi
    simpa only [hy] using hi
  have hn : ‖(x : E)‖ ≤ ‖P - Q‖ * ‖(x : E)‖ := by
    simpa only [sub_apply, hPx, hQ, sub_zero] using (P - Q).le_opNorm (x : E)
  have hx0 : ‖(x : E)‖ = 0 := by nlinarith [norm_nonneg (x : E)]
  exact Subtype.ext (norm_eq_zero.mp hx0)

/-- Finite-rank projections less than one apart in operator norm have equal rank. -/
theorem finrank_eq_of_norm_sub_lt_one (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hPQ : ‖P - Q‖ < 1)
    [FiniteDimensional ℂ P.range] [FiniteDimensional ℂ Q.range] :
    Module.finrank ℂ P.range = Module.finrank ℂ Q.range := by
  have hle (A B : E →L[ℂ] E) (hA : IsIdempotentElem A) (hAB : ‖A - B‖ < 1)
      [FiniteDimensional ℂ B.range] : Module.finrank ℂ A.range ≤ Module.finrank ℂ B.range := by
    let f : A.range →ₗ[ℂ] B.range := B.toLinearMap.rangeRestrict.comp A.range.subtype
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro x y hxy
    exact injective_on_range_of_norm_sub_lt_one A B hA hAB
      (congrArg Subtype.val hxy)
  exact le_antisymm (hle P Q hP hPQ) (hle Q P hQ (by rwa [norm_sub_rev]))

/-- A nonzero bounded projection has norm at least one. -/
theorem one_le_norm_of_ne_zero (P : E →L[ℂ] E) (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : 1 ≤ ‖P‖ := by
  have hn := norm_mul_le P P
  rw [hP] at hn
  have hpos : 0 < ‖P‖ := norm_pos_iff.mpr h0
  nlinarith

/-- A continuous family of projections on a preconnected set which vanishes at
one point vanishes everywhere. This does not require finite rank. -/
theorem eq_zero_on_preconnected {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPreconnected U) (P : X → E →L[ℂ] E)
    (hcont : ContinuousOn P U) (hid : ∀ x ∈ U, IsIdempotentElem (P x))
    {a : X} (ha : a ∈ U) (hzero : P a = 0) : ∀ x ∈ U, P x = 0 := by
  intro x hx
  by_contra hne
  have hn := one_le_norm_of_ne_zero (P x) (hid x hx) hne
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc ‖P a‖ ‖P x‖ := by
    rw [hzero, norm_zero]
    constructor <;> linarith
  obtain ⟨y, hy, hnorm⟩ := hU.intermediate_value ha hx hcont.norm hhalf
  change ‖P y‖ = 1 / 2 at hnorm
  have hny : P y ≠ 0 := by intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hge := one_le_norm_of_ne_zero (P y) (hid y hy) hny
  linarith

/-- Containment in the range of a fixed commuting projection persists under a
continuous deformation of projections on a preconnected set. -/
theorem mul_eq_self_on_preconnected {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPreconnected U) (P : X → E →L[ℂ] E)
    (hcont : ContinuousOn P U) (hid : ∀ x ∈ U, IsIdempotentElem (P x))
    (A : E →L[ℂ] E) (hA : IsIdempotentElem A) (hcomm : ∀ x ∈ U, Commute A (P x))
    {a : X} (ha : a ∈ U) (hbase : A * P a = P a) : ∀ x ∈ U, A * P x = P x := by
  have hzero : (1 - A) * P a = 0 := by rw [sub_mul, one_mul, hbase, sub_self]
  have hid' : ∀ x ∈ U, IsIdempotentElem ((1 - A) * P x) := by
    intro x hx
    exact IsIdempotentElem.mul_of_commute ((Commute.one_left _).sub_left (hcomm x hx))
      hA.one_sub (hid x hx)
  have he := eq_zero_on_preconnected hU (fun x => (1 - A) * P x)
    (continuousOn_const.mul hcont) hid' ha hzero
  intro x hx
  have hz := he x hx
  simpa only [sub_mul, one_mul, sub_eq_zero, eq_comm] using hz

/-- Rank is constant on every preconnected continuous family of finite-rank
projections, including families defined only on a subspace of parameters. -/
theorem finrank_eq_on_preconnected {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsPreconnected U) (P : X → E →L[ℂ] E)
    (hcont : ContinuousOn P U) (hid : ∀ x ∈ U, IsIdempotentElem (P x))
    (hfinite : ∀ x ∈ U, FiniteDimensional ℂ (P x).range)
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) :
    Module.finrank ℂ (P a).range = Module.finrank ℂ (P b).range := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hc : Continuous (fun x : U => P x.val) := continuousOn_iff_continuous_domRestrict.mp hcont
  have hl : IsLocallyConstant (fun x : U => Module.finrank ℂ (P x.val).range) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have he := hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (P x.val) zero_lt_one)
    filter_upwards [he] with y hy
    let : FiniteDimensional ℂ (P x.val).range := hfinite x.val x.property
    let : FiniteDimensional ℂ (P y.val).range := hfinite y.val y.property
    exact finrank_eq_of_norm_sub_lt_one _ _ (hid y.val y.property) (hid x.val x.property)
      (by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hy)
  exact hl.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩

end NLS.ProjectionRank
