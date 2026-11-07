import NLS.KdV.HillIndependentFrequencyLifting
import NLS.KdV.HminusOneHillProductZeroJacobian
import NLS.KdV.HminusOneHillProductEquationRows

/-! The common analytic independent-data frequency domain contains
ALL actual real Hill zero sequences on every physical Miura chart.
Their lifted frequencies lie in the ACTUAL signed gaps; they are gap
samples, and are not asserted to be spectral eigenvalues. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillIndependentFrequency_eq_real_balanced (σ : ℕ+ → ℝ) (c : ℝ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : ∀ m : ℕ+, hillEnergySequenceZero m d = (σ m:ℂ)) (k : ℤ) :
    hillIndependentFrequency ((c:ℂ),d) k = hillBalancedGapFrequency σ c k := by
  have hp (m : ℕ+) : hillIndependentFrequency ((c:ℂ),d) ((m:ℕ):ℤ) =
      hillBalancedGapFrequency σ c ((m:ℕ):ℤ) := by
    rw [hillIndependentFrequency_positive,hd,hillBalancedGapFrequency_pos]
    rfl
  rcases lt_trichotomy k 0 with hk | hk | hk
  · let m : ℕ+ := ⟨(-k).toNat,by omega⟩
    have he : -((m:ℕ):ℤ) = k := by
      change -(((-k).toNat:ℕ):ℤ) = k
      rw [Int.toNat_of_nonneg (by omega),neg_neg]
    rw [← he,hillIndependentFrequency_neg,hillBalancedGapFrequency_neg,hp]
  · subst k
    rw [hillIndependentFrequency_zero,hillBalancedGapFrequency_zero]
  · let m : ℕ+ := ⟨k.toNat,by omega⟩
    have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
    rw [← he,hp]

namespace HillHminusPsiBall

theorem actual_zero_data_mem_frequencyDomain (B : HillHminusPsiBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ((B.parent.miuraBall.actionBall.shift:ℂ),hillHminusPsiZeroDisplacement n ⟨q,hr⟩) ∈
      LpSequence.quadraticFrequencyDomain Real.pi := by
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hq).1 hr⟩
  intro m
  have h := (hillMiura_frequency_of_original_gap q hr u B.parent.miuraBall.actionBall.shift
    (B.parent.miuraBall.actionBall.image q (B.subset hq).1)
    (B.parent.miuraBall.actionBall.outside q (B.subset hq).1) m
    (hillHminusCanonicalPsiRealZero n m q hr) (hillHminusCanonicalPsiRealZero_mem_gap n m q hr)).1
  change hillEnergySequenceZero m (hillHminusPsiZeroDisplacement n ⟨q,hr⟩)+
    (B.parent.miuraBall.actionBall.shift:ℂ) ∈ slitPlane
  rw [hillEnergySequenceZero_real]
  exact h

theorem actual_independentFrequency_mem_signed_gap (B : HillHminusPsiBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) (k : ℤ) :
    hillIndependentFrequency ((B.parent.miuraBall.actionBall.shift:ℂ),hillHminusPsiZeroDisplacement n ⟨q,hr⟩) k ∈
      sourcePeriodicSegment (by norm_num) (by norm_num)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k := by
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hq).1 hr⟩
  rw [hillIndependentFrequency_eq_real_balanced (fun m => hillHminusCanonicalPsiRealZero n m q hr)
    B.parent.miuraBall.actionBall.shift _ (fun m => hillEnergySequenceZero_real n m ⟨q,hr⟩)]
  exact hillBalancedGapFrequency_mem_segment q hr u B.parent.miuraBall.actionBall.shift
    (B.parent.miuraBall.actionBall.image q (B.subset hq).1)
    (B.parent.miuraBall.actionBall.outside q (B.subset hq).1) _
    (fun m => hillHminusCanonicalPsiRealZero_mem_gap n m q hr) k

end HillHminusPsiBall
end NLS.KdV
