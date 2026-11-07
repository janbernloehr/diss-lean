import NLS.Articles.KdVPseudomeasures.SourceFractionalInverseGap
import NLS.Articles.KdVPseudomeasures.OriginalMiuraGapComparison
import NLS.ZakharovShabat.SourceSobolevGapRegularity
import NLS.SequenceSpaces.PeriodOneMiuraNegativeRegularity
import NLS.SequenceSpaces.WeightedSingle

/-! # Global inverse regularity throughout the negative Hilbert interval

An actual native output supplies the original Hill gaps. Their exact
Miura comparison gives the Dirac gaps, the proved NLS inverse regularity
recovers the same lift, and its literal Miura image recovers the source.
-/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem original_negative_sobolev_of_gap (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : OriginalHminusOnePotential)
    (hgap : Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*originalCanonicalGapValues q k) 2) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*(originalPeriodOneCoefficients q).val k) 2 := by
  obtain ⟨c,_,_,u,himage,_⟩ := exists_real_periodOneMiura_shift_outside_spectrum
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) 0
  have hu : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_pow] using himage
  have hdirac := memlp_miuraDiracGap_of_original_gap q u (c^2) (-r) hu hgap
  have hdirac' : Memℓp (fun k : ℤ => (Weight.sobolev (1-r) k:ℂ)*
      sourcePeriodicGapDisplacement (p := 2) (by norm_num) (by norm_num) (hillMiuraRealSource u).val k) 2 := by
    simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
      hillMiuraRealSource,hillMiuraDiracRight,hillMiuraDiracLeft,show -r+1 = 1-r by ring] using hdirac
  have hreg := (source_mem_sobolev_of_gap (by norm_num) (by norm_num) (hillMiuraRealSource u)
    (1-r) (by linarith) hdirac').1
  have hureg : Memℓp (fun k => (Weight.sobolev (1-r) k:ℂ)*u.val k) 2 := by
    simpa only [hillMiuraRealSource,hillMiuraDiagonal_fst] using hreg
  have hMiura := periodOneMiura_memlp_negative_of_lift r hr hr1 u.val hureg
  have hconst : Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*
      (periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ))).val k) 2 := by
    have hh := (single (p := 2) (Weight.sobolev (-r)) 0 ((c^2:ℝ):ℂ)).property
    change Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*
      (single (p := 2) (Weight.sobolev (-r)) 0 ((c^2:ℝ):ℂ)).val k) 2 at hh
    simpa only [single_val,periodOneL2Inclusion_apply,lp.single_apply] using hh
  convert hMiura.sub hconst using 1
  funext k
  have he := congrArg (fun a : PeriodOneHminusOne => a.val k) hu
  change (periodOneMiura u.val).val k = (originalPeriodOneCoefficients q).val k+
    (periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ))).val k at he
  change (Weight.sobolev (-r) k:ℂ)*(originalPeriodOneCoefficients q).val k =
    (Weight.sobolev (-r) k:ℂ)*(periodOneMiura u.val).val k-
      (Weight.sobolev (-r) k:ℂ)*(periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ))).val k
  rw [he]
  ring

/-- Every actual native preimage of a fractional signed Hilbert output
has the exact original H^(-r) regularity, without an inverse premise. -/
theorem original_negative_sobolev_of_native_output (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : OriginalHminusOnePotential)
    (z : WeightedCoeff (Weight.signedSobolev (-r+1/2)) 2)
    (hz : ∀ k, z.val k = hillHminusNativeCoordinate k (originalPeriodOneCoefficients q)) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*(originalPeriodOneCoefficients q).val k) 2 :=
  original_negative_sobolev_of_gap r hr hr1 q
    (originalCanonicalGaps_mem_sobolev_of_native_output (-r) (by linarith) q z hz)

end NLS.Articles.KdVPseudomeasures
