import NLS.ZakharovShabat.SourceAngularBetaSpectralData
import NLS.ZakharovShabat.SourceAngularEtaCauchyTerminal

/-! # Normalized eta remainders and actual spectral data

Isospectrality preserves the actual standard-root products and remainder
integrands. Equal Dirichlet terminals and full sheet values identify the
normalized Cauchy remainders across independently chosen annular charts.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equality of the actual normalized standard-root factors on an isospectral set. -/
theorem sourceStandardRoot_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 ψ.val n z = sourceStandardRoot hp hp1 φ.val n z := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
  rw [he.1,he.2]

theorem sourceStandardRootOmittedProduct_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n ψ.val z =
      sourceStandardRootOmittedProduct hp hp1 n φ.val z := by
  simp only [sourceStandardRootOmittedProduct, sourceStandardRootOmittedPairedFactor,
    sourceStandardRoot_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceAngularEtaRemainderIntegrand_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p))) (z : ℂ) :
    sourceAngularEtaRemainderIntegrand hp hp1 n s ψ.val z =
      sourceAngularEtaRemainderIntegrand hp hp1 n t φ.val z := by
  simp only [sourceAngularEtaRemainderIntegrand, sourceAngularIntegrand,
    sourceAngularEtaModelIntegrand, hnum,
    sourceStandardRoot_eq_of_isospectral hp hp1 φ ψ h,
    sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceAngularEtaRemainderSheetIntegrand_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p))) (w z : ℂ) :
    sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ.val w z =
      sourceAngularEtaRemainderSheetIntegrand hp hp1 n t φ.val w z := by
  simp only [sourceAngularEtaRemainderSheetIntegrand, hnum,
    sourceStandardRootOmittedProduct_eq_of_isospectral hp hp1 φ ψ h n,
    sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h]

theorem sourceAngularEtaRemainderSheetPrimitiveData_isospectral_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)))
    (c : ℂ) (R : ℝ) (w : ℂ) (F E : ℂ → ℂ) :
    SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ.val c R w F E ↔
      SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n t
        φ.val c R w F E := by
  have hseg := sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h n
  have hends := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hdisc := sourceAngularRegularSheetDisc_eq_of_isospectral hp hp1 φ ψ h c R w
  have hext := sourceAngularExteriorPrimitive_eq_of_isospectral hp hp1 φ ψ h w F 0
  have hi := sourceAngularEtaRemainderIntegrand_eq_of_isospectral hp hp1 φ ψ h n s t hnum
  have hs := sourceAngularEtaRemainderSheetIntegrand_eq_of_isospectral hp hp1 φ ψ h n s t hnum w
  constructor <;> intro D
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hseg, hends.2] using D.tendsto_right_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hseg, hends.2] using D.tendsto_right_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩

/-- Equal actual spectra and selected signed Dirichlet data give equal
Cauchy remainders even when the charts use different circles and anchors. -/
theorem SourceAngularJointAnnulusChartData.etaRemainderCauchyCandidate_isospectral
    {hp : p ≠ ⊤} {hp1 : 1 < p}
    {n : ℤ} {s t : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {W V W' V' : Set (CoeffPair p)}
    {c c' : ℤ → ℂ} {T T' : ℤ → ℝ} {r R r' R' : ℝ} {z₀ z₀' : ℂ}
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (E : SourceAngularJointAnnulusChartData hp hp1 n t W' V' c' T' r' R' z₀')
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (hψ : ψ.val ∈ V) (hφ : φ.val ∈ V')
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n φ.val : Coeff p)))
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
    (hσ : sourceDirichletSign hp hp1 ψ n = sourceDirichletSign hp hp1 φ n)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (ρ' : ℝ) (hrρ' : r' < ρ') (hρR' : ρ' < R') :
    sourceAngularEtaRemainderCauchyCandidate hp hp1 n s (c n) r R z₀ ρ ψ.val =
      sourceAngularEtaRemainderCauchyCandidate hp hp1 n t (c' n) r' R' z₀' ρ' φ.val := by
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ.val n
  · rw [D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ.val hψ ρ hend,
      E.etaRemainderCauchyCandidate_eq_zero_of_endpoint φ.val hφ ρ'
        ((sourceAngularDirichletTerminalIsEndpoint_isospectral_iff hp hp1 φ ψ h n hμ).mp hend)]
  · have hw := sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ.val n
      (((D.disc_family ψ.val hψ).contour_family.2 n).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ.val hψ).dirichlet_mem_ball n)))
      (fun h => hend (Or.inl h)) (fun h => hend (Or.inr h))
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n)
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ.val n hw
    have hC := D.eta_cauchy_sheet_primitive_data ψ.val hψ ρ hrρ hρR w hw
    have hC' := (sourceAngularEtaRemainderSheetPrimitiveData_isospectral_iff
      hp hp1 φ ψ h n s t hnum (c n) r w _ _).mp hC
    have ha := sourceDirichletTerminal_eq_of_isospectral_root_sign hp hp1 φ ψ h n hμ hσ
    have hseg : sourcePeriodicSegment hp hp1 φ.val n ⊆ ball (c n) r := by
      rw [← sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h n]
      exact D.gap_enclosed ψ.val hψ
    have hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n ∈
        sourceAngularRegularSheetDisc hp φ.val (c n) r w := by
      rw [← hμ, ← sourceAngularRegularSheetDisc_eq_of_isospectral hp hp1 φ ψ h]
      exact ⟨D.terminal_enclosed ψ.val hψ,hbase.1⟩
    have hroot : sourceAngularRootSheet hp w
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,φ.val) =
        sourceAntiDiscriminantCandidate hp hp1 φ.val
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n) := by
      calc
        _ = sourceAngularRootSheet hp w
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n,ψ.val) := by
          rw [hμ,sourceAngularRootSheet_eq_of_isospectral hp hp1 φ ψ h]
        _ = w := hbase.2
        _ = _ := ha
    have heq := E.etaRemainderCauchyCandidate_eq_normalized_terminal φ.val hφ ρ' hrρ' hρR'
      hC' hseg hw hb hroot
    dsimp only at heq
    rw [← hμ, hbase.2] at heq
    exact heq.symm

end NLS.ZakharovShabat
