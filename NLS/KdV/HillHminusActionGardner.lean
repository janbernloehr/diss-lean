import NLS.KdV.HillHminusActionHamiltonianVector
import NLS.KdV.HillActionSourceStationarity
import NLS.KdV.HillCartesianActionSourceVariations

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- ORIGINAL actions commute under the genuine H-minus-one Gardner bracket
at every original real source, including low indices and closed gaps. -/
theorem hillOriginalActions_hminus_Gardner_commute
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ))
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 m 0 : ℂ)) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) = 0 := by
  let h := hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 m m.pos 0
  have heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0 :=
    hillEnergyContourHamiltonianSource_mem_even _ _ _ _ _ _
  rw [←NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,
    hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q m G hG hGM,map_neg,
    hillOriginalAction_hminus_fderiv_original q n F hF hFM h heven,
    ←hillRealSourceMoment_gradient q.val q.property.1 q.property.2 n n.pos 0]
  exact neg_eq_zero.mpr (hillRealSourceMoment_physicalMomentHamiltonianSource_fderiv
    q.val q.property.1 q.property.2 n m n.pos m.pos 0 0)

/-- The ORIGINAL complex Cartesian coordinate has the POSITIVE i action
rotation for the genuine Gardner bracket. This sign follows from the
proved negative physical-source/positive Gardner-vector comparison. -/
theorem hillOriginalCartesian_action_hminus_Gardner_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (Z J : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 m 0 : ℂ)) :
    NLS.Poisson.hminusGardnerBracket Z J (hillOriginalHminusSource q.val) =
      I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ) *
        hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos := by
  obtain ⟨K,hK,hKM,hD⟩ := exists_hillSpectralCartesian_actionSource_variations
    q.val q.property.1 q.property.2 (by simp) (by simp [IsRealHillPotential]) n n.pos
  let h := hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 m m.pos 0
  have heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0 :=
    hillEnergyContourHamiltonianSource_mem_even _ _ _ _ _ _
  have hZK : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = K (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hZM,hKM] with p hp hk
    exact hp.trans hk.symm
  have he := hillHminusPhysicalGerm_fderiv_original q Z K hZ hK hZK h heven
  rw [←NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,
    hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q m J hJ hJM,map_neg,he,hD m m.pos]
  ring

end NLS.KdV
