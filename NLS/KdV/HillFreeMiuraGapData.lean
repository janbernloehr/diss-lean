import NLS.KdV.HillNativeDirichletFirstVariation
import NLS.KdV.HillNativeMidpointStationarity
import NLS.ZakharovShabat.SourceActionMidpointCircleExistence

/-! Exact positive collapsed frequency data of ANY actual Miura gap
ball at zero native potential, retaining every original Hill index. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraGapBall

def freeFrequencyMidpoint (B : HillHminusMiuraGapBall) (n : ℕ+) : ℂ :=
  sourceStandardRootMidpoint (by norm_num) (by norm_num)
    (hillMiuraDiagonal (B.actionBall.lift 0)) (n:ℕ)

theorem freeFrequencyMidpoint_pos (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    0 < (B.freeFrequencyMidpoint n).re := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := B.diracSum_re_pos_of_real n 0 h0 hr
  change 0 < (2*B.freeFrequencyMidpoint n).re at hp
  rw [two_mul,add_re] at hp
  linarith

theorem freeFrequencyMidpoint_real (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    (B.freeFrequencyMidpoint n).im=0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift 0,B.actionBall.lift_real 0 h0 hr⟩
  have hre := hillMiuraDiracPair_real u (n:ℕ)
  change ((hillMiuraDiracLeft u.val (n:ℕ)+hillMiuraDiracRight u.val (n:ℕ))/2).im=0
  simp [add_im,hre.1,hre.2]

theorem freeDiracGap_zero (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift 0))) (periodOnePotential_mem _) (n:ℕ)=0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := B.diracSum_re_pos_of_real n 0 h0 hr
  have hs : B.diracSum n 0 ≠ 0 := fun he => (ne_of_gt hp) (by rw [he]; rfl)
  have hg := (B.canonical_gapSquare_eq n 0 h0).symm
  rw [hillHminusCanonicalGapSquare_zero] at hg
  change (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift 0))) (periodOnePotential_mem _) (n:ℕ))^2*
      (B.diracSum n 0)^2=0 at hg
  by_contra hne
  exact (pow_ne_zero 2 hne) ((mul_eq_zero.mp hg).resolve_right (pow_ne_zero 2 hs))

theorem freeSourceGap_zero (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.actionBall.lift 0)) (n:ℕ)=0 := by
  rw [sourcePeriodicGapDisplacement_apply,B.freeDiracGap_zero h0 n]

theorem freeFrequencyMidpoint_energy (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    (B.freeFrequencyMidpoint n)^2-(B.actionBall.shift:ℂ)=((Real.pi:ℂ)*n)^2 := by
  have he := (B.canonical_energyMidpoint_eq_locally_zero h0 n).eq_of_nhds.symm
  rw [← hillHminusCanonicalDirichlet_eq_midpoint_zero,hillHminusCanonicalDirichlet_zero_eq_sq] at he
  change (B.freeFrequencyMidpoint n)^2+_ ^2/4-(B.actionBall.shift:ℂ)=_ at he
  rw [B.freeDiracGap_zero h0 n,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,add_zero] at he
  exact he

end NLS.KdV.HillHminusMiuraGapBall
