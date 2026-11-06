import NLS.SequenceSpaces.UniformTailContinuity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Hilbert norm continuity from scalar coordinates and squared norms

Finite Fourier truncations split the squared norm exactly. Continuity of
coordinates and of the total squared norm therefore controls the tails
locally and yields continuity in the full sequence norm.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem norm_sq_split_truncate (a : Coeff 2) (s : Finset ℤ) :
    ‖a‖^2=‖a-truncate s a‖^2+‖truncate s a‖^2 := by
  have hn (b : Coeff 2) : ‖b‖^2=∑' k : ℤ, ‖b k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) b
  have hs (b : Coeff 2) : Summable (fun k : ℤ => ‖b k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) b).summable
  rw [hn a,hn (a-truncate s a),hn (truncate s a),← (hs (a-truncate s a)).tsum_add (hs (truncate s a))]
  apply tsum_congr
  intro k
  by_cases hk : k∈s <;> simp [truncate_apply,hk]

theorem continuousAt_of_coordinatewise_of_norm_sq
    {X : Type*} [TopologicalSpace X] (f : X → Coeff 2) (x : X)
    (hc : ∀ k : ℤ, ContinuousAt (fun y => f y k) x)
    (hn : ContinuousAt (fun y => ‖f y‖^2) x) : ContinuousAt f x := by
  apply continuousAt_of_coordinatewise_of_uniform_tails f x hc
  intro ε hε
  have ht : Tendsto (fun s : Finset ℤ => ‖f x-truncate s (f x)‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : Finset ℤ => f x) atTop (𝓝 (f x))).sub (tendsto_truncate (by norm_num : (2:ℝ≥0∞)≠⊤) (f x))).norm
  obtain ⟨s,hs⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  have hfin := (continuousAt_truncate_of_coordinatewise f x s hc).norm.pow 2
  have he : (fun y => ‖f y-truncate s (f y)‖^2) =
      (fun y => ‖f y‖^2-‖truncate s (f y)‖^2) := by
    funext y
    linarith [norm_sq_split_truncate (f y) s]
  have htail : ContinuousAt (fun y => ‖f y-truncate s (f y)‖) x := by
    have hsq : ContinuousAt (fun y => ‖f y-truncate s (f y)‖^2) x := by
      rw [he]
      exact hn.sub hfin
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (htail.eventually (gt_mem_nhds hs))
  exact ⟨s,V,hVo,hxV,fun y hy => (hV hy).le⟩
/-- A real signed sequence has twice the positive squared amplitude sum.
The zero mode is included in the natural sum and assumed to vanish. -/
theorem norm_sq_eq_twice_tsum_nat (a : Coeff 2) (h0 : a 0=0)
    (hneg : ∀ k : ℤ, ‖a (-k)‖=‖a k‖) :
    ‖a‖^2=2*(∑' n : ℕ, ‖a (n:ℤ)‖^2) := by
  have hs : Summable (fun k : ℤ => ‖a k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) a).summable
  have hn : Summable (fun n : ℕ => ‖a (n:ℤ)‖^2) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => (n:ℤ)) from Nat.cast_injective)
  have hneg' : Summable (fun n : ℕ => ‖a (-((n:ℤ)+1))‖^2) := by
    simpa only [hneg,← Nat.cast_one (R := ℤ),← Nat.cast_add] using
      (summable_nat_add_iff 1).mpr hn
  have he := tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ‖a k‖^2) hn hneg'
  have hshift := hn.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,h0,norm_zero,zero_pow (by decide : 2≠0),zero_add] at hshift
  simp only [hneg,← Nat.cast_one (R := ℤ),← Nat.cast_add] at he
  have hnorm : ‖a‖^2=∑' k : ℤ, ‖a k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) a
  rw [hnorm,he,hshift]
  ring

end NLS.Coeff
