import NLS.Articles.KdVPseudomeasures.OriginalHillRayleigh
import NLS.KdV.HminusOneMiuraIsospectral

/-!
# A single actual Dirac isospectral set contains all original Miura lifts

The common shift is chosen below the common lowest Hill energy. Both the
zero-frequency exclusion and every nonzero-frequency algebraic count are
therefore retained in the actual original Dirac spectral data.
-/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ZakharovShabat

/-- All members of the ENTIRE original isospectral set have bounded real
Miura lifts in ONE actual Dirac isospectral set at ONE common large shift. -/
theorem exists_originalIsospectral_lifts_in_one_dirac_isospectral_set
    (q : OriginalHminusOnePotential) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∃ u₀ : PeriodOneRealL2,
      periodOneMiura u₀.val = originalPeriodOneCoefficients q+
        periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ p ∈ originalIsospectralSet q, ∃ u : PeriodOneRealL2,
        ‖u.val‖ ≤ R ∧
        periodOneMiura u.val = originalPeriodOneCoefficients p+
          periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) ∧
        hillMiuraRealSource u ∈ sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀) := by
  obtain ⟨c,hc,hbig,R,hR,hlift⟩ := exists_uniform_real_originalIsospectral_Miura_shift q
    (max A (|originalHillLabels q 0|+1))
  have hAc : A < c := (le_max_left _ _).trans_lt hbig
  have hlarge : |originalHillLabels q 0|+1 < c := (le_max_right _ _).trans_lt hbig
  have henergy : -((c:ℂ)^2) ∉ singularHillSpectrum q.val := by
    intro hz
    have h := (originalHillLabels_zero_lowest q).2 _ hz
    rw [← ofReal_pow,← ofReal_neg,ofReal_re] at h
    nlinarith [abs_nonneg (originalHillLabels q 0),neg_le_abs (originalHillLabels q 0)]
  obtain ⟨u₀,_,hu₀⟩ := hlift q (mem_originalIsospectralSet_self q)
  refine ⟨c,hc,hAc,u₀,hu₀,R,hR,fun p hp => ?_⟩
  obtain ⟨u,hu,himage⟩ := hlift p hp
  refine ⟨u,hu,himage,?_⟩
  apply hillMiuraRealSource_mem_isospectral_of_shifted_images
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients p) u₀ u ((c:ℂ)^2)
      hu₀ himage
  · intro z
    simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hp z
  · simpa only [periodOneOriginal_originalPeriodOneCoefficients] using henergy

/-- Fully original Hill isospectrality fixes the actual normalized physical
discriminant, including its sign and all complex energies. -/
theorem originalHillDiscriminant_eq_of_isospectral
    (q p : OriginalHminusOnePotential) (hp : p ∈ originalIsospectralSet q) :
    originalHillDiscriminant p = originalHillDiscriminant q := by
  obtain ⟨c,_,_,u₀,hu₀,R,_,hlift⟩ :=
    exists_originalIsospectral_lifts_in_one_dirac_isospectral_set q 0
  obtain ⟨u,_,hu,hiso⟩ := hlift p hp
  have hd := (mem_sourceIsospectralSet_iff_discriminant_eq
    (by norm_num) (by norm_num) (hillMiuraRealSource u₀) (hillMiuraRealSource u)).mp hiso
  funext z
  change hillHminusDiscriminant (originalPeriodOneCoefficients p) z =
    hillHminusDiscriminant (originalPeriodOneCoefficients q) z
  rw [hillHminusDiscriminant_eq_miura_of_shifted_image _ _ _ z hu,
    hillHminusDiscriminant_eq_miura_of_shifted_image _ _ _ z hu₀]
  exact congrFun hd (Complex.sqrt (z+(c:ℂ)^2))

/-- The normalized physical discriminant characterizes full original
isospectrality, retaining all physical algebraic multiplicities. -/
theorem mem_originalIsospectralSet_iff_discriminant_eq
    (q p : OriginalHminusOnePotential) :
    p ∈ originalIsospectralSet q ↔ originalHillDiscriminant p = originalHillDiscriminant q := by
  refine ⟨originalHillDiscriminant_eq_of_isospectral q p,fun hd z => ?_⟩
  rw [← analyticOrderNatAt_originalHillDiscriminant p z,
    ← analyticOrderNatAt_originalHillDiscriminant q z,hd]

end NLS.Articles.KdVPseudomeasures
