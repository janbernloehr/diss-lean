import NLS.KdV.HillCartesianAllPeriodicInvariant
import NLS.KdV.HillCartesianMatrixNormalization

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The full ORIGINAL complex Cartesian Gardner matrix at EVERY
mean-zero original real source with the selected gaps open. Actual
indexed transport and its all-periodic limit discharge the endpoint premise. -/
theorem hillIntrinsicCartesianGardnerBracket_eq_matrix
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0)
    (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0) :
    hillIntrinsicCartesianGardnerBracket n m σ τ q = hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  obtain ⟨r,_,_,hrΔ,hterminal,hInv⟩ :=
    exists_hillAllPeriodicIsospectralSource_preserving_normalized_bracket q hmean n m σ τ hgapn hgapm
  have hlabels := hillRealLabels_eq_of_discriminant_eq r q hrΔ
  have hrn : hillRealGapHalfLength r.val r.property.1 r.property.2 n ≠ 0 := by
    unfold hillRealGapHalfLength
    rw [hlabels]
    exact hgapn
  have hrm : hillRealGapHalfLength r.val r.property.1 r.property.2 m ≠ 0 := by
    unfold hillRealGapHalfLength
    rw [hlabels]
    exact hgapm
  obtain ⟨hF,hFM⟩ := hillSignedCartesianHminusGerm_spec r n σ hrn
  obtain ⟨hG,hGM⟩ := hillSignedCartesianHminusGerm_spec r m τ hrm
  have hBr : hillIntrinsicCartesianGardnerBracket n m σ τ r = hillOriginalComplexGardnerMatrixEntry σ τ n m :=
    hillSignedCartesians_hminus_Gardner_endpoint_matrix r n m σ τ hrn hrm hterminal _ _ hF hG hFM hGM
  have hPr : hillSignedSpectralCartesian σ n r * hillSignedSpectralCartesian τ m r ≠ 0 :=
    mul_ne_zero (hillSignedSpectralCartesian_ne_zero_open r n σ hrn)
      (hillSignedSpectralCartesian_ne_zero_open r m τ hrm)
  have hPq : hillSignedSpectralCartesian σ n q * hillSignedSpectralCartesian τ m q ≠ 0 :=
    mul_ne_zero (hillSignedSpectralCartesian_ne_zero_open q n σ hgapn)
      (hillSignedSpectralCartesian_ne_zero_open q m τ hgapm)
  unfold hillIntrinsicNormalizedCartesianBracket at hInv
  rw [hBr] at hInv
  have hc := (div_eq_div_iff hPr hPq).mp hInv
  have hp := hillOriginalComplexGardnerMatrixEntry_mul_product_isospectral q r n m σ τ
    (fun E => (hrΔ E).symm)
  have hz : (hillIntrinsicCartesianGardnerBracket n m σ τ q - hillOriginalComplexGardnerMatrixEntry σ τ n m) *
      (hillSignedSpectralCartesian σ n r * hillSignedSpectralCartesian τ m r) = 0 := by
    rw [sub_mul,←hc]
    exact sub_eq_zero.mpr hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hPr)

/-- ALL FOUR genuine ORIGINAL signed Cartesian Gardner entries now hold
at every original mean-zero source with open selected gaps. Every analytic
H-minus-one representative matching the ORIGINAL real L2 germ is allowed;
no terminal, finite-gap or flow-invariance premise remains. -/
theorem hillSignedCartesians_hminus_Gardner_original_open_matrix
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0)
    (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) =
      hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  rw [←hillIntrinsicCartesianGardnerBracket_eq_of_physical_germs q n m σ τ
    hgapn hgapm F G hF hG hFM hGM]
  exact hillIntrinsicCartesianGardnerBracket_eq_matrix q hmean n m σ τ hgapn hgapm

end NLS.KdV
