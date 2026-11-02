import NLS.Articles.KdVPseudomeasures.WeakStarEndpoint
import NLS.Fourier.PeriodicFourierLebesgueDuality

/-! # Weak-star convergence of original periodic pseudomeasures

This adapter uses the already proved full dual isometry of the actual
distribution space, preserving the library's normalized physical pairing.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Original periodic pseudomeasures with the actual Wiener weak-star topology. -/
def pseudomeasureWeakStar (u : PeriodicFourierLebesgue L Weight.one ⊤) :
    WeakDual ℂ (PeriodicFourierLebesgue L Weight.one 1) :=
  StrongDual.toWeakDual (pseudomeasureDualIsometry u)

/-- Bounded coefficient convergence on original distributions implies genuine
Wiener weak-star convergence; the conclusion is on the original predual. -/
theorem tendsto_pseudomeasureWeakStar_of_bounded_coefficients
    {α : Type*} {l : Filter α}
    (x : α → PeriodicFourierLebesgue L Weight.one ⊤)
    (a : PeriodicFourierLebesgue L Weight.one ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => (x k).val (mode n)) l (𝓝 (a.val (mode n)))) :
    Tendsto (fun k => pseudomeasureWeakStar (x k)) l (𝓝 (pseudomeasureWeakStar a)) := by
  let e := (unweightedCoefficients (L := L) ⊤).trans Coeff.reflection
  have heb : Bornology.IsBounded (range (fun k => e (x k))) := by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨k, rfl⟩
    simpa only [LinearIsometryEquiv.norm_map] using hM _ ⟨k, rfl⟩
  have hec (n : ℤ) : Tendsto (fun k => e (x k) n) l (𝓝 (e a n)) := by
    simpa [e, unweightedCoefficients_apply] using hc n
  have ht := Coeff.tendsto_wienerWeakStar_of_bounded_coefficients
    (fun k => e (x k)) (e a) heb hec
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro b
  have h := tendsto_iff_forall_eval_tendsto_topDualPairing.mp ht
    (unweightedCoefficients 1 b)
  change Tendsto (fun k => Coeff.dualPairing (e (x k))
      (unweightedCoefficients 1 b)) l
    (𝓝 (Coeff.dualPairing (e a) (unweightedCoefficients 1 b))) at h
  change Tendsto (fun k => unweightedDualEquiv (p := 1) (by simp) (x k) b) l
    (𝓝 (unweightedDualEquiv (p := 1) (by simp) a b))
  simpa only [unweightedDualEquiv_apply, Coeff.dualPairing_apply,
    e, LinearIsometryEquiv.trans_apply, Coeff.reflection_apply,
    unweightedCoefficients_apply, neg_neg] using h

end NLS.Fourier.PeriodicFourierLebesgue
