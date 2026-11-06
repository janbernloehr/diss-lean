import NLS.KdV.HillCriticalOwnAmplitudeTerms
import NLS.SequenceSpaces.NatL2AnalyticRealization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual high original own-amplitude sequence in the critical
weighted complex Hilbert norm, with a fixed natural-index encoding. -/
def hillNativeCriticalOwnAmplitudeTail (w : SpectralWeight) (N : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : Coeff 2 :=
  Coeff.natL2OfFunction (fun k => hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q)

def hillNativeCriticalOwnDualAmplitudeTail (w : SpectralWeight) (N : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : Coeff 2 :=
  Coeff.natL2OfFunction (fun k => hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q)

/-- Both original own-amplitude tails are genuinely complex Hilbert
analytic on each bounded source ball. Every coordinate is the original
critical normalized scalar value, so the total constructor has no fallback. -/
theorem exists_hillNativeCriticalOwnAmplitudeTails_analytic_bound (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ w : SpectralWeight, ∀ N : ℕ, N0≤N →
      AnalyticOnNhd ℂ (hillNativeCriticalOwnAmplitudeTail h0q h0r w N)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) ∧
      AnalyticOnNhd ℂ (hillNativeCriticalOwnDualAmplitudeTail h0q h0r w N)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) ∧
      ∀ q∈ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B,
        ‖hillNativeCriticalOwnAmplitudeTail h0q h0r w N q‖^2≤C*(B^2+512*B^4) ∧
        ‖hillNativeCriticalOwnDualAmplitudeTail h0q h0r w N q‖^2≤C*(B^2+512*B^4) ∧
        (∀ k : ℕ, hillNativeCriticalOwnAmplitudeTail h0q h0r w N q (Equiv.intEquivNat.symm k)=
          hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q) ∧
        (∀ k : ℕ, hillNativeCriticalOwnDualAmplitudeTail h0q h0r w N q (Equiv.intEquivNat.symm k)=
          hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q) := by
  obtain ⟨C,hC,Nb,hNb,hbound⟩ :=
    exists_hillNativeCriticalOwnAmplitudeTerms_uniform_square_bound h0q h0r B hB
  obtain ⟨Na,hNa,hanalytic⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_common_analytic h0q h0r B
  refine ⟨C,hC,max Nb Na,hNb.trans (le_max_left _ _),?_⟩
  intro w N hN
  have hNB : Nb≤N := (le_max_left _ _).trans hN
  have hNA : Na≤N := (le_max_right _ _).trans hN
  have hqB (q : WeightedCoeff w.doubleIndex.toWeight 2)
      (hq : q∈ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) : ‖q‖≤B :=
    (show ‖q‖<B by simpa only [mem_ball,dist_zero_right] using hq).le
  refine ⟨?_,?_,?_⟩
  · exact Coeff.analyticOnNhd_natL2OfFunction_of_summable_sq_bound
      (fun q k => hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q) _ isOpen_ball
      (fun k => (hanalytic w (k+N) (by omega)).1) (C*(B^2+512*B^4))
      (fun q hq => (hbound w N hNB q (hqB q hq)).1)
  · exact Coeff.analyticOnNhd_natL2OfFunction_of_summable_sq_bound
      (fun q k => hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q) _ isOpen_ball
      (fun k => (hanalytic w (k+N) (by omega)).2) (C*(B^2+512*B^4))
      (fun q hq => (hbound w N hNB q (hqB q hq)).2)
  · intro q hq
    obtain ⟨⟨hsp,hbp⟩,⟨hsm,hbm⟩⟩ := hbound w N hNB q (hqB q hq)
    exact ⟨(Coeff.norm_natL2OfFunction_sq_eq_tsum _ hsp).le.trans hbp,
      (Coeff.norm_natL2OfFunction_sq_eq_tsum _ hsm).le.trans hbm,
      Coeff.natL2OfFunction_apply_of_summable_sq _ hsp,
      Coeff.natL2OfFunction_apply_of_summable_sq _ hsm⟩

end NLS.KdV
