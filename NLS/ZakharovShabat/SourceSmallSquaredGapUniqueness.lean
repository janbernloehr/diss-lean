import NLS.ZakharovShabat.SymmetricSignedGapLocalInverse
import NLS.ZakharovShabat.SourceSquaredGapUniquenessReduction
import NLS.ZakharovShabat.SourceHilbertActionTrace

/-! # Squared-gap spectral uniqueness for small Hilbert sources

The actual action trace makes the source norm an isospectral invariant.
Thus the symmetric all-left-endpoint representative of a small source is
still small. The analytic local signed-gap inverse at zero then proves
actual squared-gap spectral uniqueness on a source ball, without any
global openness or injectivity hypothesis.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- Actual Hilbert isospectral sources have the same original coefficient-pair norm. -/
theorem sourceHilbert_norm_eq_of_isospectral (φ ψ : realTypeSourceSubmodule 2)
    (h : ψ ∈ sourceIsospectralSet (by simp) φ) : ‖ψ.val‖ = ‖φ.val‖ := by
  have he : ‖ψ.val‖^2/2 = ‖φ.val‖^2/2 := by
    rw [← sourceHilbert_sum_actions_eq_half_norm_sq ψ,
      ← sourceHilbert_sum_actions_eq_half_norm_sq φ]
    apply tsum_congr
    intro n
    exact congrArg Complex.re (sourceRealAction_eq_of_isospectral (by simp) (by norm_num) φ ψ h n)
  nlinarith [norm_nonneg ψ.val,norm_nonneg φ.val]

/-- Real symmetric Fourier coordinates have norm at most their original source-pair norm. -/
theorem norm_symmetric_source_coordinates_le (a : RealCoeff 2) :
    ‖a‖ ≤ ‖(symmetricRealSourceCoefficients 2 a).val‖ := by
  have he : ‖a‖ ≤ ‖(symmetricSourceCoefficients 2 a).snd‖ := by
    apply lp.norm_mono (by norm_num)
    intro n
    simp
  exact he.trans (WithLp.norm_snd_le _ _)

/-- The nonpositive signed-gap representative can be chosen within the original source norm. -/
theorem exists_symmetric_coordinates_isospectral_nonpos_signed_gaps_norm_le
    (φ : realTypeSourceSubmodule 2) :
    ∃ a : RealCoeff 2,
      symmetricRealSourceCoefficients 2 a ∈ sourceIsospectralSet (by simp) φ ∧
      (∀ n, symmetricSourceSignedGapMap (by simp) (by norm_num) a n ≤ 0) ∧
      ‖a‖ ≤ ‖φ.val‖ := by
  obtain ⟨a,ha,hneg⟩ := exists_symmetric_coordinates_isospectral_nonpos_signed_gaps φ
  refine ⟨a,ha,hneg,?_⟩
  exact (norm_symmetric_source_coordinates_le a).trans_eq
    (sourceHilbert_norm_eq_of_isospectral φ _ ha)

/-- Equal squared periodic gaps determine the actual spectral data of any two sufficiently
small real Hilbert sources, including all algebraic multiplicities. No global signed-gap
injectivity or openness is assumed. -/
theorem exists_small_source_squared_gap_spectral_uniqueness :
    ∃ ε : ℝ, 0 < ε ∧ ∀ φ ψ : realTypeSourceSubmodule 2,
      ‖φ.val‖ < ε → ‖ψ.val‖ < ε →
      (∀ n,
        (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
          (periodOnePotential_mem _) n)^2 =
        (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val)
          (periodOnePotential_mem _) n)^2) →
      ψ ∈ sourceIsospectralSet (by simp) φ := by
  obtain ⟨G,_,_,hl,_,_⟩ := exists_symmetricSourceSignedGap_localInverse_zero
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hl
  refine ⟨ε,hε,fun φ ψ hφ hψ hgaps => ?_⟩
  obtain ⟨a,ha,ha0,hanorm⟩ :=
    exists_symmetric_coordinates_isospectral_nonpos_signed_gaps_norm_le φ
  obtain ⟨b,hb,hb0,hbnorm⟩ :=
    exists_symmetric_coordinates_isospectral_nonpos_signed_gaps_norm_le ψ
  have htransport (θ : realTypeSourceSubmodule 2) (c : RealCoeff 2)
      (hc : symmetricRealSourceCoefficients 2 c ∈ sourceIsospectralSet (by simp) θ) (n : ℤ) :
      (sourceSignedGapSequence (by simp) (by norm_num) (symmetricSourceCoefficients 2 c) n)^2 =
        (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential θ.val)
          (periodOnePotential_mem _) n)^2 := by
    have hs := sourceSignedGapSequence_sq_of_reflection_fixed (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 c) (symmetricRealSourceCoefficients_reflection_fixed c) n
    simp only [symmetricRealSourceCoefficients_val] at hs
    rw [hs]
    have he := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 c)) (periodOnePotential θ.val)
      (periodOnePotential_mem _) (periodOnePotential_mem _) hc.1 hc.2
    simp only [canonicalPeriodicGap,he.1,he.2]
  have hF : symmetricSourceSignedGapMap (by simp) (by norm_num) a =
      symmetricSourceSignedGapMap (by simp) (by norm_num) b := by
    ext n
    have he := (htransport φ a ha n).trans ((hgaps n).trans (htransport ψ b hb n).symm)
    have hima := sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 a) n
    have himb := sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 b) n
    simp only [symmetricRealSourceCoefficients_val] at hima himb
    have hr := congrArg Complex.re he
    simp only [pow_two,mul_re,hima,himb,mul_zero,sub_zero] at hr
    change symmetricSourceSignedGapMap (by simp) (by norm_num) a n *
      symmetricSourceSignedGapMap (by simp) (by norm_num) a n =
      symmetricSourceSignedGapMap (by simp) (by norm_num) b n *
      symmetricSourceSignedGapMap (by simp) (by norm_num) b n at hr
    nlinarith [ha0 n,hb0 n]
  have ha' := hball (show a ∈ Metric.ball (0 : RealCoeff 2) ε by
    simpa only [Metric.mem_ball,dist_zero_right] using hanorm.trans_lt hφ)
  have hb' := hball (show b ∈ Metric.ball (0 : RealCoeff 2) ε by
    simpa only [Metric.mem_ball,dist_zero_right] using hbnorm.trans_lt hψ)
  have hab : a = b := ha'.symm.trans ((congrArg G hF).trans hb')
  subst b
  exact ⟨hb.1.symm.trans ha.1,fun z => (hb.2 z).symm.trans (ha.2 z)⟩

/-- For a sufficiently small source, its entire actual isospectral set is exactly its
squared-gap fiber inside one fixed source ball. The ball restriction is essential to
the proved local statement and is not removed here. -/
theorem exists_small_source_isospectralSet_eq_squared_gap_fiber :
    ∃ ε : ℝ, 0 < ε ∧ ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖ < ε →
      sourceIsospectralSet (by simp) φ =
        {ψ : realTypeSourceSubmodule 2 | ‖ψ.val‖ < ε ∧ ∀ n,
          (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
            (periodOnePotential_mem _) n)^2 =
          (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val)
            (periodOnePotential_mem _) n)^2} := by
  obtain ⟨ε,hε,hunique⟩ := exists_small_source_squared_gap_spectral_uniqueness
  refine ⟨ε,hε,fun φ hφ => ?_⟩
  ext ψ
  constructor
  · intro hψ
    refine ⟨?_,fun n => ?_⟩
    · exact (sourceHilbert_norm_eq_of_isospectral φ ψ hψ).trans_lt hφ
    · have he := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential φ.val)
        (periodOnePotential_mem _) (periodOnePotential_mem _) hψ.1 hψ.2
      simp only [canonicalPeriodicGap,he.1,he.2]
  · intro hψ
    exact hunique φ ψ hφ hψ.1 hψ.2

end NLS.ZakharovShabat
