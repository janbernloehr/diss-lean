import NLS.KdV.HillTraceStationaryTerminalAngle

/-! # Actual Dirichlet first-variation data

The data assert first derivatives of actual trace, Dirichlet root and signed
sheet maps. No flow, normalized numerator or angle derivative is prescribed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

structure HillDirichletVelocityData (q : RealPeriodOneHillPotential)
    (k : ℕ) (hk : 1≤k) (V : Coeff 2) (K : ℂ) : Prop where
  parity : V∈Coeff.paritySubspace 0
  trace_stationary : ∀ z : ℂ,
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q.val)) V=0
  root_velocity : ∀ a : Coeff 2 → ℂ, AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) →
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) →
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) →
      (fderiv ℂ a (SpectralWeight.one.toCoeff q.val)) V=
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) (a (SpectralWeight.one.toCoeff q.val))*K
  sheet_velocity : ∀ a : Coeff 2 → ℂ, AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) →
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) →
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) →
      (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) (SpectralWeight.one.toCoeff q.val)) V=
        (hillL2Discriminant (SpectralWeight.one.toCoeff q.val) (a (SpectralWeight.one.toCoeff q.val))*
          deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val)) (a (SpectralWeight.one.toCoeff q.val)))*K

theorem HillDirichletVelocityData.terminal_angle
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (ε : Coeff 2 → ℂ) (hε : DifferentiableAt ℂ ε (SpectralWeight.one.toCoeff q.val))
    (hterminal : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      cosineGapPoint (hillRealGapCenter r.val r.property.1 r.property.2 k)
        (hillRealGapHalfLength r.val r.property.1 r.property.2 k) (ε (SpectralWeight.one.toCoeff r.val))=
          (hillDirichletEnergy r.val r.property.1 r.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff r.val))=hillDirichletGapSine r.val r.property.1 r.property.2 k hk)
    (V : Coeff 2) (K : ℂ) (hv : HillDirichletVelocityData q k hk V K) :
    (fderiv ℂ ε (SpectralWeight.one.toCoeff q.val)) (V)=
      I*hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*K := by
  exact fderiv_hillDirichletTerminalAngle_of_trace_stationary q k hk hgap ε hε hterminal V
    hv.trace_stationary hv.parity K hv.root_velocity hv.sheet_velocity

end NLS.KdV
