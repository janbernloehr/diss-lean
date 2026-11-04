import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralTerminalCurve
import NLS.FunctionalAnalysis.ComplexSpectralSheetEndpoint

/-! The actual complete native indexed flow reaches a periodic terminal.
Its fixed original spectral sheet gives the bounded real ODE. Open-gap
endpoints have nonzero acceleration; collapsed gaps are already terminal. -/
noncomputable section
open Set Complex Filter Topology NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem exists_originalHillSpectralFlow_endpoint (k : ℕ+) (q : OriginalHminusOnePotential) :
    ∃ t : ℝ, hillHminusDirichletSheet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=0 ∧
      (hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=
        (originalHillLabels q (2*(k:ℕ)-1):ℂ) ∨
       hillHminusCanonicalDirichlet k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=
        (originalHillLabels q (2*(k:ℕ)):ℂ)) := by
  let γ : ℝ → PeriodOneHminusOne := fun t => originalPeriodOneCoefficients (originalHillSpectralFlow k q t)
  let μ : ℝ → ℂ := fun t => hillHminusCanonicalDirichlet k (γ t)
  let S : ℝ → ℂ := fun t => hillHminusDirichletSheet k (γ t)
  let Δ : ℂ → ℂ := originalHillDiscriminant q
  let a : ℝ := originalHillLabels q (2*(k:ℕ)-1)
  let b : ℝ := originalHillLabels q (2*(k:ℕ))
  have hΔC : Continuous Δ := (analyticOnNhd_hillHminusDiscriminant_energy (originalPeriodOneCoefficients q)).continuous
  have hΔ'C : Continuous (deriv Δ) := continuous_deriv_hillHminusDiscriminant (originalPeriodOneCoefficients q)
  have hEnds : (Δ (a:ℂ))^2-4=0 ∧ (Δ (b:ℂ))^2-4=0 := by
    constructor
    · exact (hillHminusLabels_roots_iff _ (originalPeriodOneCoefficients_real q) _).mpr ⟨2*(k:ℕ)-1,rfl⟩
    · exact (hillHminusLabels_roots_iff _ (originalPeriodOneCoefficients_real q) _).mpr ⟨2*(k:ℕ),rfl⟩
  have hsimple (hopen : a < b) : Δ (a:ℂ)*deriv Δ (a:ℂ) ≠ 0 ∧ Δ (b:ℂ)*deriv Δ (b:ℂ) ≠ 0 := by
    have hgap : hillHminusCanonicalGapSquare k (originalPeriodOneCoefficients q) ≠ 0 := by
      rw [hillHminusCanonicalGapSquare_eq_real _ (originalPeriodOneCoefficients_real q) k]
      change ((b:ℂ)-(a:ℂ))^2 ≠ 0
      exact pow_ne_zero 2 (sub_ne_zero.mpr (fun he => (ne_of_gt hopen) (ofReal_inj.mp he)))
    have hs := hillHminusRadicand_deriv_at_open_gap_endpoints_ne_zero _ (originalPeriodOneCoefficients_real q) k hgap
    constructor
    · intro hz
      apply hs.1
      rw [deriv_hillHminusRadicand]
      change 2*Δ (a:ℂ)*deriv Δ (a:ℂ)=0
      linear_combination 2*hz
    · intro hz
      apply hs.2
      rw [deriv_hillHminusRadicand]
      change 2*Δ (b:ℂ)*deriv Δ (b:ℂ)=0
      linear_combination 2*hz
  exact exists_endpoint_of_bounded_complex_sheetODE μ S Δ a b
    (originalHillSpectralFlow_dirichlet_im_eq_zero k q) (originalHillSpectralFlow_sheet_im_eq_zero k q)
    (hasDerivAt_originalHillSpectralFlow_terminal k q) (originalHillSpectralFlow_dirichlet_mem_initial_gap k q)
    (originalHillSpectralFlow_sheet_sq_fixed k q)
    (hillHminusDiscriminant_im_eq_zero_of_real _ (originalPeriodOneCoefficients_real q))
    (hillHminusDiscriminant_energy_derivative_im_eq_zero _ (originalPeriodOneCoefficients_real q))
    hΔC hΔ'C hEnds
    (fun y hy hz => (hillHminusRadicand_zero_in_gap_iff_endpoint _ (originalPeriodOneCoefficients_real q) k y hy).mp hz)
    hsimple

end NLS.Articles.KdVPseudomeasures
