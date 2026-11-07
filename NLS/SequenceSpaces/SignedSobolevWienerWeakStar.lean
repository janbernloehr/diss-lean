import NLS.SequenceSpaces.WienerWeakStar
import NLS.SequenceSpaces.SignedSobolevBilinearPairing

/-! # Exact signed-weight Wiener preduals

This endpoint dependency holds for every real signed weight order, including
the actual KdV endpoint target order `1/2-r` for `0 ≤ r < 1/2`.
The physical bilinear pairing reverses one Fourier index. On real distributions
this agrees with using the conjugated real-symmetric Wiener test.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- Actual weak-star realization with opposite-order Wiener predual. -/
def signedSobolevWeakStar (s : ℝ) (a : WeightedCoeff (Weight.signedSobolev s) ⊤) :
    WeakDual ℂ (WeightedCoeff (Weight.signedSobolev (-s)) 1) :=
  StrongDual.toWeakDual (signedSobolevBilinearPairing s a)

theorem signedSobolevWeakStar_apply (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) ⊤)
    (b : WeightedCoeff (Weight.signedSobolev (-s)) 1) :
    signedSobolevWeakStar s a b = ∑' n : ℤ, a.val n * b.val (-n) :=
  signedSobolevBilinearPairing_apply s a b

/-- Bounded raw coefficient convergence gives actual opposite-weight weak-star
convergence, retaining arbitrary real Sobolev order. -/
theorem tendsto_signedSobolevWeakStar_of_bounded_coefficients
    (s : ℝ) {α : Type*} {l : Filter α}
    (x : α → WeightedCoeff (Weight.signedSobolev s) ⊤)
    (a : WeightedCoeff (Weight.signedSobolev s) ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => (x k).val n) l (𝓝 (a.val n))) :
    Tendsto (fun k => signedSobolevWeakStar s (x k)) l (𝓝 (signedSobolevWeakStar s a)) := by
  let e := weightIsometry (Weight.signedSobolev s) ⊤
  have heb : Bornology.IsBounded (range (fun k => e (x k))) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    simpa only [LinearIsometryEquiv.norm_map] using hM _ ⟨k, rfl⟩
  have hec (n : ℤ) : Tendsto (fun k => e (x k) n) l (𝓝 (e a n)) :=
    (hc n).const_mul (Weight.signedSobolev s n : ℂ)
  have ht := Coeff.tendsto_wienerWeakStar_of_bounded_coefficients
    (fun k => e (x k)) (e a) heb hec
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro b
  exact tendsto_iff_forall_eval_tendsto_topDualPairing.mp ht
    (Coeff.reflection (weightIsometry (Weight.signedSobolev (-s)) 1 b))

/-- Finite Fourier approximations converge in the weighted weak-star topology
even at infinity, where norm density of finite sequences is unavailable. -/
theorem tendsto_signedSobolevWeakStar_truncate (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) ⊤) :
    Tendsto (fun f : Finset ℤ => signedSobolevWeakStar s (truncate _ ⊤ f a))
      atTop (𝓝 (signedSobolevWeakStar s a)) := by
  apply tendsto_signedSobolevWeakStar_of_bounded_coefficients
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖a‖, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact norm_truncate_le _ _ f a
  · intro n
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with f hf
    exact (truncate_apply _ _ f a n).trans (if_pos (hf (by simp)))

end NLS.WeightedCoeff
