import NLS.Articles.KdVKdV2Frequencies.GlobalStrongLpFrequencyActionCharts
import NLS.Articles.KdVKdV2Frequencies.StrongPairHilbertFrequencyCalibration
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization

/-! ONE physically calibrated frequency map on the ENTIRE original raw
ell1 positive action cone, with genuine unweighted ellr analytic extensions
for EVERY r>1. All exponents have the SAME raw frequency coefficients. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_hilbert_frequency_with_cubic_normalization :
    ∃ V : Set ActionSpace, ∃ G : ActionSpace → ActionSpace,
      IsOpen V ∧ positiveQuadrant⊆V ∧ AnalyticOnNhd ℂ G V ∧
      ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
        G (originalActionInclusion b.val) n=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨V,_H,G,hV,hcone,_hH,hG,_hd,_he,hrec⟩ :=
    exists_global_analytic_gradient_with_original_physical_frequencies
  refine ⟨V,G,hV,hcone,hG,?_⟩
  intro b n
  rw [hrec]
  congr 1
  push_cast
  ring

theorem GlobalRoughAbelianForwardData.exists_actual_raw_ellOne_kdv_frequency
    (D : GlobalRoughAbelianForwardData) :
    ∃ ω : Coeff 1 → ℤ → ℂ,
      (∀ a : Coeff 1, ∀ j : ℤ, j≤0 → ω a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (ω a j).im=0) ∧
      (∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
        ω (originalActionToCoeffOne b.val) (n : ℤ)=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ r : ℝ≥0∞, ∀ hr : 1<r, letI : Fact (1 ≤ r) := ⟨hr.le⟩;
        ∃ U : Set (Coeff 1), ∃ F : Coeff 1 → Coeff r,
          IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ F U ∧
          (∀ a∈U, ∀ j : ℤ, j≤0 → F a j=0) ∧
          ∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, F a j=ω a j := by
  obtain ⟨V,G,_hV,hcone,hG,hrec⟩ := exists_hilbert_frequency_with_cubic_normalization
  let ω := fun (a : Coeff 1) (j : ℤ) => if hj : 0<j then
    G (rawActionHilbertInclusion a) (positiveIntegerIndex j hj) else 0
  have hzero (a : Coeff 1) (j : ℤ) (hj : j≤0) : ω a j=0 := dif_neg (by omega)
  have hpos (a : Coeff 1) (n : ℕ+) : ω a (n : ℤ)=G (rawActionHilbertInclusion a) n := by
    have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
    change (if hj : (0 : ℤ)<n then G (rawActionHilbertInclusion a) (positiveIntegerIndex (n : ℤ) hj) else 0)=_
    rw [dif_pos hn]
    have he : positiveIntegerIndex (n : ℤ) hn=n := by
      apply Subtype.ext
      simp only [positiveIntegerIndex,Int.toNat_natCast]
      rfl
    rw [he]
  refine ⟨ω,hzero,?_,?_,?_⟩
  · intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_strongLp_pair_of_nonnegative_actions D (r := 2) (by norm_num) a ha
      rw [←hnj,hpos,←hQ,←strong_pair_correction_eq_hilbert_frequency V G hcone hG hrec P z hz hzr n]
      exact physicalMiuraFrequencyChart_real D P.physicalChart (P.roughPotential z)
        (P.rough_real z hz hzr) (P.rough_zero z hz) (P.rough_mem z hz) n
    · rw [hzero a j (by omega)];rfl
  · intro b n
    rw [hpos,rawActionHilbertInclusion_original]
    exact hrec b n
  · intro r hr
    let : Fact (1 ≤ r) := ⟨hr.le⟩
    obtain ⟨U,F,hU,hCU,hF,hFzero,hFrec⟩ := exists_global_strong_physical_lp_action_packet D hr
    refine ⟨U,F,hU,hCU,hF,hFzero,?_⟩
    intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      obtain ⟨P,z,hz,hzr,hQ⟩ := exists_strongLp_pair_of_nonnegative_actions D hr a ha
      rw [←hnj,←hQ,hFrec P z hz hzr,P.positive z hz n,hpos]
      exact strong_pair_correction_eq_hilbert_frequency V G hcone hG hrec P z hz hzr n
    · rw [hFzero a (hCU ha) j (by omega),hzero a j (by omega)]

end NLS.Articles.KdVKdV2Frequencies
