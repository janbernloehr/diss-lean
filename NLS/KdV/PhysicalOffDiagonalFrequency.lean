import NLS.KdV.PhysicalMiuraFrequencyChart

/-! The actual off-diagonal physical second-moment correction. The
own Hill gap corresponds to both opposite Dirac frequency labels. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.PhysicalMiuraFrequencyChart

def offDiagonalCorrection (B : PhysicalMiuraFrequencyChart) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  let ψ := hillMiuraDiagonal (B.psi.miura.lift q)
  (-12 : ℂ)*(B.atlas.weightedSecondMomentSum (n : ℤ) ψ-
    (n : ℂ)*(B.atlas.moment (n : ℤ) (n : ℤ) 2 ψ-B.atlas.moment (n : ℤ) (-(n : ℤ)) 2 ψ))

theorem offDiagonalCorrection_eq_physical (B : PhysicalMiuraFrequencyChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈B.domain) (n : ℕ+) :
    B.offDiagonalCorrection n (hillOriginalHminusSource q.val)=
      -12*((∑' k : ℕ, (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2)-
        (n : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos (n : ℕ) 2) := by
  have hs := (B.psi.physical_weighted_secondMoment_sum q (B.domain_subset hq) B.real_lift
    (B.outside_shift _ (B.domain_subset hq).1) B.shift B.energyShift_eq B.atlas n
    (B.absolute_moments _ hq (n : ℤ))).2
  have hd := B.psi.physical_secondMoment_eq_miura_pair q (B.domain_subset hq) B.real_lift
    (B.outside_shift _ (B.domain_subset hq).1) B.shift B.energyShift_eq B.atlas n n
  rw [offDiagonalCorrection,←hs,←hd]

end NLS.KdV.PhysicalMiuraFrequencyChart
