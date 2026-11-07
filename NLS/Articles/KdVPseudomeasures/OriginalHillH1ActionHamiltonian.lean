import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapEnergyIsospectral
import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerActionTruncation

/-! The ACTUAL physical H1 KdV Hamiltonian depends only on the original
canonical actions. Strong genuine finite-gap approximants retain the same
native products and full original spectrum before passing energy limits. -/
noncomputable section
open Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1KdVHamiltonian_eq_of_native_products
    (p q : RealSignedHilbert (signedStepOrder 0 1))
    (hp : ∀ n : ℕ+, ((hillIntegerSobolevEquiv 1).equiv p).val.val.val (n:ℤ)*
        ((hillIntegerSobolevEquiv 1).equiv p).val.val.val (-(n:ℤ))=
      ((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ)*
        ((hillIntegerSobolevEquiv 1).equiv q).val.val.val (-(n:ℤ))) :
    hillH1KdVHamiltonian p=hillH1KdVHamiltonian q := by
  have htP := (analyticAt_hillH1KdVHamiltonian p).continuousAt.tendsto.comp
    (hillIntegerFiniteGapApproximation_tendsto 1 p)
  have htQ := (analyticAt_hillH1KdVHamiltonian q).continuousAt.tendsto.comp
    (hillIntegerFiniteGapApproximation_tendsto 1 q)
  have he (N : ℕ) : hillH1KdVHamiltonian (hillIntegerFiniteGapApproximation 1 p N)=
      hillH1KdVHamiltonian (hillIntegerFiniteGapApproximation 1 q N) :=
    hillH1KdVHamiltonian_eq_of_finiteGap_isospectral
      (hillIntegerFiniteGapApproximation 1 q N) (hillIntegerFiniteGapApproximation 1 p N)
      (hillIntegerFiniteGapApproximation_mem 1 q N)
      (hillIntegerFiniteGapApproximation_isospectral_of_products 1 p q hp N)
  have hfun : (fun N => hillH1KdVHamiltonian (hillIntegerFiniteGapApproximation 1 p N))=
      (fun N => hillH1KdVHamiltonian (hillIntegerFiniteGapApproximation 1 q N)) := funext he
  change Tendsto (fun N => hillH1KdVHamiltonian (hillIntegerFiniteGapApproximation 1 p N))
    atTop (𝓝 (hillH1KdVHamiltonian p)) at htP
  rw [hfun] at htP
  exact tendsto_nhds_unique htP htQ

/-- The SAME original canonical inverse transforms the physical energy
into an action-dependent function on ALL real signed H^(3/2). -/
theorem hillH1CanonicalHamiltonian_eq_of_products
    (w z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (hz : ∀ n : ℕ+, w.val.val.val (n:ℤ)*w.val.val.val (-(n:ℤ))=
      z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ))) :
    hillH1CanonicalHamiltonian w=hillH1CanonicalHamiltonian z := by
  apply hillH1KdVHamiltonian_eq_of_native_products
  simpa only [(hillIntegerSobolevEquiv 1).equiv.apply_symm_apply] using hz

/-- Every H1 member of the ENTIRE original isospectral set has the same
actual physical KdV Hamiltonian; no finite-gap hypothesis remains. -/
theorem hillH1KdVHamiltonian_eq_of_original_isospectral
    (p q : RealSignedHilbert (signedStepOrder 0 1))
    (hp : originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 p) ∈
      originalIsospectralSet (originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 q))) :
    hillH1KdVHamiltonian p=hillH1KdVHamiltonian q := by
  have hd := (mem_originalIsospectralSet_iff_discriminant_eq _ _).mp hp
  have hn : hillRealDiscriminantData (hillIntegerSourceInclusion 1 p)=
      hillRealDiscriminantData (hillIntegerSourceInclusion 1 q) := by
    simpa only [← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hd
  have hprod := (hillRealDiscriminantData_eq_iff_native_products _ _).mp hn
  apply hillH1KdVHamiltonian_eq_of_native_products
  intro n
  simpa only [← hillIntegerSobolevEquiv_inclusion,hillIntegerTargetInclusion_apply] using hprod n

end NLS.Articles.KdVPseudomeasures
