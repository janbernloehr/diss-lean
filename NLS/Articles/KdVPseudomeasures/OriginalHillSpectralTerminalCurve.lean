import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralGlobalFlow
import NLS.KdV.HillRealGapSheetGeometry

/-! Actual terminal equations for the complete native flow, expressed
on its FIXED original spectral curve. Its Dirichlet coordinate stays
in the same original gap and its prescribed sheet is real. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem hasDerivAt_originalHillSpectralFlow_terminal (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    HasDerivAt (fun τ => hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q τ)))
      (hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))/2) t ∧
    HasDerivAt (fun τ => hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q τ)))
      (originalHillDiscriminant q (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)))*
        deriv (originalHillDiscriminant q) (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)))/2) t := by
  let γ : ℝ → PeriodOneHminusOne := fun τ => originalPeriodOneCoefficients (originalHillSpectralFlow k q τ)
  have hγ := hasDerivAt_originalHillSpectralFlow_coefficients k q t
  have hq : γ t ∈ hillHminusCanonicalDirichletDomain :=
    real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real _)
  have he : hillHminusDiscriminant (γ t)=originalHillDiscriminant q :=
    (mem_originalIsospectralSet_iff_discriminant_eq q _).mp (originalHillSpectralFlow_mem_isospectral k q t)
  constructor
  · simpa only [if_pos rfl,ite_true,γ] using hasDerivAt_hillHminusDirichlet_on_spectralCurve k k γ t hγ hq
  · simpa only [if_pos rfl,ite_true,he,γ] using hasDerivAt_hillHminusSheet_on_spectralCurve k k γ t hγ hq

theorem originalHillSpectralFlow_dirichlet_im_eq_zero (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))).im=0 := by
  rw [hillHminusCanonicalDirichlet_eq_real _ (originalPeriodOneCoefficients_real _)]
  rfl

theorem originalHillSpectralFlow_dirichlet_mem_initial_gap (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))).re ∈
      Icc (originalHillLabels q (2*(k:ℕ)-1)) (originalHillLabels q (2*(k:ℕ))) := by
  have hb := hillHminusDirichletLabels_mem_gap
    (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)) (originalPeriodOneCoefficients_real _) k
  change originalHillLabels (originalHillSpectralFlow k q t) (2*(k:ℕ)-1) ≤ _ ∧
    _ ≤ originalHillLabels (originalHillSpectralFlow k q t) (2*(k:ℕ)) at hb
  rw [(mem_originalIsospectralSet_iff_originalHillLabels q _).mp (originalHillSpectralFlow_mem_isospectral k q t)] at hb
  simpa only [hillHminusCanonicalDirichlet_eq_real _ (originalPeriodOneCoefficients_real _),ofReal_re,Set.mem_Icc] using hb

theorem originalHillSpectralFlow_sheet_im_eq_zero (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    (hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))).im=0 := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_originalHillSpectralFlow_terminal k q t).1
  have he : (fun τ => (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q τ))).im)=
      fun _ => (0 : ℝ) := funext (originalHillSpectralFlow_dirichlet_im_eq_zero k q)
  have hz : (hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))/2).im=0 := by
    apply hd.unique
    simpa only [Function.comp_def,Complex.imCLM_apply,he] using hasDerivAt_const t (0 : ℝ)
  simp only [div_ofNat_im] at hz
  linarith

theorem originalHillSpectralFlow_sheet_sq_fixed (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    (hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)))^2=
      (originalHillDiscriminant q (hillHminusCanonicalDirichlet k
        (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))))^2-4 := by
  have he : hillHminusDiscriminant (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=originalHillDiscriminant q :=
    (mem_originalIsospectralSet_iff_discriminant_eq q _).mp (originalHillSpectralFlow_mem_isospectral k q t)
  rw [hillHminusDirichletSheet_sq _ _ (real_mem_hillHminusCanonicalDirichletDomain _
    (originalPeriodOneCoefficients_real _)),he]

end NLS.Articles.KdVPseudomeasures
