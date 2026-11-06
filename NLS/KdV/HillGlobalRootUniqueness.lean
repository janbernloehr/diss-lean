import NLS.KdV.HillGlobalDifferentialUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelian_normalized_roots_unique_off_selected
    (roots other : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hother : other ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (hrootsPeriods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hotherPeriods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr other n k = 0)
    (j : ℕ) (hj : j+1 ≠ n) : roots j = other j := by
  have hψ : hillAbelianPsiCandidate roots n (roots j : ℂ) = 0 :=
    (hillAbelianPsiCandidate_zero_iff q hq hr roots hroots n hn _).mpr ⟨j,hj,rfl⟩
  have he := congrFun (hillAbelian_normalized_candidate_unique q hq hr roots other hroots hother n hn
    hrootsPeriods hotherPeriods) (roots j : ℂ)
  rw [hψ,zero_div] at he
  have ho : hillAbelianPsiCandidate other n (roots j : ℂ) = 0 :=
    (div_eq_zero_iff.mp he.symm).resolve_right (hillAbelianCandidatePeriod_own_ne_zero q hq hr other hother n hn)
  obtain ⟨k,_,hk⟩ := (hillAbelianPsiCandidate_zero_iff q hq hr other hother n hn _).mp ho
  have hkr : other k = roots j := by simpa only [ofReal_re] using congrArg Complex.re hk
  have hkj : k = j := by
    by_contra hne
    rcases hillRealGap_exterior_to_other_gap q hq hr (j+1) (k+1) (by omega) (by omega) (by omega)
      (roots j) (hroots j) with hl | hu
    · linarith [(hother k).1]
    · linarith [(hother k).2]
  simpa only [hkj] using hkr.symm

end NLS.KdV
