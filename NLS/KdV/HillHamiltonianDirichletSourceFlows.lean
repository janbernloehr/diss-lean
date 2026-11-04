import NLS.KdV.HillContourHamiltonianSources
import NLS.KdV.HillAbelianActionResiduePeriods
import NLS.KdV.HillDirichletGardnerBrackets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The constructed physical source pairs with the Dirichlet gradient
as the genuine Gardner integral; its boundary term is actually zero. -/
theorem hillPhysicalMomentHamiltonianSource_dirichlet_pairing
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (m : ℕ) :
    hillPhysicalDirectionPairing
      (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k hk m))
      (hillDirichletGradientCurve q n hn)=
      ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
        (hillPhysicalMomentGradient q.val q.property.1 q.property.2 k m) x*
          deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x := by
  let f := NLS.LinearVolterra.extend (hillPhysicalMomentGradient q.val q.property.1 q.property.2 k m)
  let g := NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)
  have hF := hillPhysicalMomentGradient_H1 q.val q.property.1 q.property.2 k hk m
  have hG := hillDirichletGradient_H1 q n hn
  have hf : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hF.2.2.integrable (by norm_num))
  have hg : IntervalIntegrable (deriv g) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hG.2.2.integrable (by norm_num))
  have hi := integral_mul_deriv_eq_complex hF.1 hG.1 hf hg
  have h0 : g 0=0 := by
    simpa only [g,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillDirichletGradientCurve_endpoints q n hn).1
  have h1 : g 1=0 := by
    simpa only [g,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillDirichletGradientCurve_endpoints q n hn).2
  change (∫ x in (0 : ℝ)..1,f x*deriv g x)=f 1*g 1-f 0*g 0-
    (∫ x in (0 : ℝ)..1,deriv f x*g x) at hi
  rw [h0,h1,mul_zero,mul_zero,sub_self,zero_sub] at hi
  rw [hillPhysicalMomentHamiltonianSource,hillEnergyContourHamiltonianSource_pairing,hi]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillEnergyGradientContour (SpectralWeight.one.toCoeff q.val)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m)
    (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)
    (hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k)
    (add_nonneg (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).1
      (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).2.1.le)
    (continuousOn_hillPhysicalMomentGradientWeight q.val q.property.1 q.property.2 k hk m)] with x hx
  have hd : deriv f x= _ := hx.deriv
  rw [hd]
  rfl

/-- An actual analytic Dirichlet branch has the exact sheet times
residue derivative along the genuine physical moment coefficient source. -/
theorem hillDirichletBranch_physicalMomentHamiltonianSource_fderiv
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (m : ℕ)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) :
    (fderiv ℂ a (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k hk m))=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
          hillPhysicalMomentDirichletResidue q k n hn m := by
  rw [hillDirichletGradient_represents_branch q n hn a ha ha0 hz]
  rw [← hillPhysicalDirectionPairing_apply]
  rw [hillPhysicalMomentHamiltonianSource_dirichlet_pairing q k n hk hn m,
    hillPhysicalMomentGradient_dirichlet_bracket_eq_sheet_mul_residue q k n hk hn m]

/-- At every positive Dirichlet label there is one genuine analytic
root branch carrying all physical moment source derivatives at once. -/
theorem exists_hillDirichletBranch_physicalMomentHamiltonianSource_fderiv
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a : Coeff 2 → ℂ, AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) ∧
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) ∧
      ∀ k : ℕ, ∀ hk : 1≤k, ∀ m : ℕ,
        (fderiv ℂ a (SpectralWeight.one.toCoeff q.val))
          (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k hk m))=
          hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
              hillPhysicalMomentDirichletResidue q k n hn m := by
  obtain ⟨a,ha,ha0,hz⟩ := exists_hillL2Dirichlet_analytic_root_branch
    (SpectralWeight.one.toCoeff q.val) q.property.2
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  exact ⟨a,ha,ha0,hz,fun k hk m =>
    hillDirichletBranch_physicalMomentHamiltonianSource_fderiv q k n hk hn m a ha ha0 hz⟩

/-- The terminal differential evaluated on an actual Dirichlet branch
variation equals its checked residue coefficient wherever the sheet is
nonzero. No division by a vanishing terminal root is claimed. -/
theorem hillDirichletBranch_regular_abelian_tangent
    (q : RealPeriodOneHillPotential) (k n j : ℕ) (hk : 1≤k) (hn : 1≤n) (hj : 1≤j)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 j hj : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (hreg : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 j hj)≠0) :
    (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
      (hillDirichletEnergy q.val q.property.1 q.property.2 j hj)/
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 j hj))*
      (fderiv ℂ a (SpectralWeight.one.toCoeff q.val))
        (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k hk 0))=
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
        (hillDirichletEnergy q.val q.property.1 q.property.2 j hj)*hillPhysicalMomentDirichletResidue q k j hj 0 := by
  rw [hillDirichletBranch_physicalMomentHamiltonianSource_fderiv q k j hk hj 0 a ha ha0 hz]
  rw [← mul_assoc,div_mul_cancel₀ _ hreg]

/-- On the regular terminal locus, the actual Dirichlet branch source
variations contract with the normalized differential to the signed
Kronecker period. This is not yet differentiation of the full phase. -/
theorem hillDirichletBranches_regular_abelian_tangent_sum
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n)
    (a : ℕ → Coeff 2 → ℂ)
    (ha : ∀ j : ℕ, AnalyticAt ℂ (a j) (SpectralWeight.one.toCoeff q.val))
    (ha0 : ∀ j : ℕ, a j (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega) : ℂ))
    (hz : ∀ j : ℕ, ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a j p)=0)
    (hreg : ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))≠0) :
    Tendsto (fun N => ∑ j∈Finset.range N,
      (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
        (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))/
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega)))*
      (fderiv ℂ (a j) (SpectralWeight.one.toCoeff q.val))
        (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k hk 0)))
      atTop (𝓝 (-(if k=n then 1 else 0 : ℂ))) := by
  apply (hillPhysicalActionDirichletResidue_abelian_sum q k n hk hn).congr'
  apply Eventually.of_forall
  intro N
  symm
  apply Finset.sum_congr rfl
  intro j _
  exact hillDirichletBranch_regular_abelian_tangent q k n (j+1) hk hn (by omega) (a j)
    (ha j) (ha0 j) (hz j) (hreg j)

end NLS.KdV
