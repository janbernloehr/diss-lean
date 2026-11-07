import NLS.SequenceSpaces.UniformDualCoefficientLimits
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Bounded coefficient convergence at the pseudomeasure endpoint

Independent endpoint dependency for arXiv:1610.00278v1, Appendix B.1(ii).
The topology in the conclusion is the actual weak-star topology of the
Wiener predual, not the norm topology or the weak topology of l-infinity.
These results do not construct the KdV flow or its Birkhoff map.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace NLS.Coeff

/-- A bounded coefficient sequence regarded as a weak-star Wiener functional. -/
def wienerWeakStar (a : Coeff ⊤) : WeakDual ℂ (Coeff 1) :=
  StrongDual.toWeakDual (dualPairing a)

@[simp] theorem wienerWeakStar_apply (a : Coeff ⊤) (b : Coeff 1) :
    wienerWeakStar a b = ∑' n : ℤ, a n * b n := rfl

/-- Bounded coefficient convergence implies convergence against every Wiener
test, along any filter. No finite source exponent is assumed. -/
theorem tendsto_wienerWeakStar_of_bounded_coefficients
    {α : Type*} {l : Filter α} (x : α → Coeff ⊤) (a : Coeff ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => x k n) l (𝓝 (a n))) :
    Tendsto (fun k => wienerWeakStar (x k)) l (𝓝 (wienerWeakStar a)) := by
  have hd : Bornology.IsBounded (range (fun k => x k - a)) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M + ‖a‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM _ ⟨k, rfl⟩) le_rfl)
  have hz (n : ℤ) : Tendsto (fun k => (x k - a) n) l (𝓝 0) := by
    simpa using (hc n).sub_const (a n)
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro b
  have ht : Tendsto (fun k => dualPairing b (x k - a)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [eventually_small_dualPairing_of_bounded_coefficientwise
      (p := 1) (q := ⊤) (by simp) (fun k => x k - a) hd hz b ε hε] with k hk
    simpa only [dist_zero_right] using hk b (fun _ => le_rfl)
  have he (k : α) : dualPairing b (x k - a) =
      wienerWeakStar (x k) b - wienerWeakStar a b := by
    rw [map_sub]
    simp only [dualPairing_apply, wienerWeakStar_apply]
    congr 1 <;> apply tsum_congr <;> intro n <;> exact mul_comm _ _
  have ht' : Tendsto (fun k => wienerWeakStar (x k) b - wienerWeakStar a b)
      l (𝓝 0) := by simpa only [he] using ht
  exact (tendsto_sub_nhds_zero_iff).mp ht'

/-- Weak-star convergence always implies convergence of each coefficient. -/
theorem tendsto_coefficients_of_wienerWeakStar
    {α : Type*} {l : Filter α} (x : α → Coeff ⊤) (a : Coeff ⊤)
    (h : Tendsto (fun k => wienerWeakStar (x k)) l (𝓝 (wienerWeakStar a)))
    (n : ℤ) : Tendsto (fun k => x k n) l (𝓝 (a n)) := by
  have ht := tendsto_iff_forall_eval_tendsto_topDualPairing.mp h
    (lp.single 1 n (1 : ℂ))
  change Tendsto (fun k => wienerWeakStar (x k) (lp.single 1 n 1)) l
    (𝓝 (wienerWeakStar a (lp.single 1 n 1))) at ht
  simpa [wienerWeakStar_apply, lp.single_apply, Pi.single_apply] using ht

/-- On a bounded family the weak-star and coefficient convergence criteria
coincide. This is the bounded-family part of Appendix B.1(ii)(a)-(b). -/
theorem tendsto_wienerWeakStar_iff_of_bounded
    {α : Type*} {l : Filter α} (x : α → Coeff ⊤) (a : Coeff ⊤)
    (hb : Bornology.IsBounded (range x)) :
    Tendsto (fun k => wienerWeakStar (x k)) l (𝓝 (wienerWeakStar a)) ↔
      ∀ n : ℤ, Tendsto (fun k => x k n) l (𝓝 (a n)) :=
  ⟨fun h => tendsto_coefficients_of_wienerWeakStar x a h,
    tendsto_wienerWeakStar_of_bounded_coefficients x a hb⟩

end NLS.Coeff
