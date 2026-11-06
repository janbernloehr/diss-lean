import NLS.KdV.HillAbelianInterpolationContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The physical moment's Dirichlet Cauchy coefficient after factoring
out the actual terminal sheet root, with its original factor one half. -/
def hillPhysicalMomentDirichletResidue (q : RealPeriodOneHillPotential)
    (k n : ℕ) (hn : 1≤n) (m : ℕ) : ℂ :=
  (2*deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))⁻¹*
    ∮ z in C((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ),
      hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k),
      hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m z*
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) z/
          (z-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))

theorem hillPhysicalMomentGradient_dirichlet_bracket_eq_sheet_mul_residue
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (m : ℕ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
      (hillPhysicalMomentGradient q.val q.property.1 q.property.2 k m) x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
          hillPhysicalMomentDirichletResidue q k n hn m := by
  rw [hillPhysicalMomentGradient_dirichlet_bracket_eq_residue q k n hk hn m]
  dsimp only [hillPhysicalMomentDirichletResidue]
  rw [div_eq_mul_inv,mul_assoc]

/-- The exact action-residue contraction with every normalized Abelian
numerator converges to the signed Kronecker period. This is a spectral
residue identity; identifying it with the actual phase variation is separate. -/
theorem hillPhysicalActionDirichletResidue_abelian_sum
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) :
    Tendsto (fun N => ∑ j∈Finset.range N,
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
        (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
          hillPhysicalMomentDirichletResidue q k (j+1) (by omega) 0)
      atTop (𝓝 (-(if k=n then 1 else 0 : ℂ))) := by
  let p := SpectralWeight.one.toCoeff q.val
  let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let c : ℂ := hillRealGapCenter q.val q.property.1 q.property.2 k
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k
  let a := hillPhysicalMomentGradientWeight p 0
  have hR : 0≤R := add_nonneg (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).1
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).2.1.le
  have ht := hillLabelledAbelianInterpolation_weighted_contour q.val q.property.1 q.property.2 n hn
    a c R hR (continuousOn_hillPhysicalMomentGradientWeight q.val q.property.1 q.property.2 k hk 0)
    (hillRealGapContour_sphere_subset q.val q.property.1 q.property.2 k hk)
  have hperiod := hillAbelianSelectedGlobalPsi_intrinsic_periods q.val q.property.1 q.property.2 n hn k hk
  have hroot : (∮ z in C(c,R),ψ z/hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 z)=
      ∮ z in C(c,R),ψ z/hillL2RealCutRoot p z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only
    rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q.val q.property.1 q.property.2
      (hillRealGapContour_sphere_subset q.val q.property.1 q.property.2 k hk hz)]
  rw [hroot] at hperiod
  have hweight : (∮ z in C(c,R),a z*ψ z)=
      -(Real.pi : ℂ)⁻¹*(∮ z in C(c,R),ψ z/hillL2RealCutRoot p z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR
    intro z _
    dsimp only [a,hillPhysicalMomentGradientWeight]
    rw [pow_zero,mul_one]
    ring
  have hright : (1/2 : ℂ)*(∮ z in C(c,R),a z*ψ z)= -(if k=n then 1 else 0 : ℂ) := by
    rw [hweight]
    calc
      _ = -((2*(Real.pi : ℂ))⁻¹*(∮ z in C(c,R),ψ z/hillL2RealCutRoot p z)) := by
        simp only [div_eq_mul_inv,one_mul,mul_inv_rev]
        ring
      _ = _ := by rw [hperiod]
  have hleft (N : ℕ) :
      (1/2 : ℂ)*(∑ j∈Finset.range N,
        (ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))/
          deriv (hillL2DirichletCharacteristic p)
            (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega)))*
          ∮ z in C(c,R),a z*hillL2DirichletCharacteristic p z/
            (z-(hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega) : ℂ)))=
        ∑ j∈Finset.range N,ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
          hillPhysicalMomentDirichletResidue q k (j+1) (by omega) 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [hillPhysicalMomentDirichletResidue,a,p,c,R]
    simp only [div_eq_mul_inv,one_mul,mul_inv_rev]
    ring
  have hh := ht.const_mul (1/2 : ℂ)
  have hh' : Tendsto (fun N => ∑ j∈Finset.range N,
      ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))*
        hillPhysicalMomentDirichletResidue q k (j+1) (by omega) 0)
      atTop (𝓝 ((1/2 : ℂ)*(∮ z in C(c,R),a z*ψ z))) :=
    hh.congr' (Eventually.of_forall hleft)
  rw [hright] at hh'
  exact hh'

end NLS.KdV
