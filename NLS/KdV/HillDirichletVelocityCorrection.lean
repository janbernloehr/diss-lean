import NLS.KdV.HillGardnerOpenCorrection
import NLS.KdV.HillDirichletVelocityOpenCorrection
import NLS.KdV.HillDirichletVelocityClosedCorrection

/-! # Actual regular Abelian correction variations at open gaps -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Uniform per-index formula for the actual regular correction when the
selected angle gap is open. The index being summed may be open or closed. -/
theorem fderiv_hillRegularAbelianCorrection_velocity_extension
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hnopen : hillRealGapHalfLength q hq hr n≠0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk)
    (V : Coeff 2) (K : ℕ → ℂ)
    (hv : HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k)) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      V =
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)*
        K k -
      (if k=n then 1 else 0)*
        (I*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)*
          K n) := by
  by_cases hc : hillRealGapHalfLength q hq hr k=0
  · have hkn : k≠n := by intro h;subst k;exact hnopen hc
    rw [fderiv_hillRegularAbelianCorrection_closed_velocity_extension_eq_zero q hq hr h0q h0r n k hn hk hc C hC hmatch V (K k) hv,
      hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed q hq hr n k hn hk hkn hc,
      if_neg hkn,zero_mul,zero_mul,sub_zero]
  · rw [fderiv_hillRegularAbelianCorrection_open_velocity_extension q hq hr h0q h0r n k hn hk hc C hC hmatch V (K k) hv]
    by_cases hkn : k=n
    · subst k; rfl
    · simp only [if_neg hkn,zero_mul]

end NLS.KdV
