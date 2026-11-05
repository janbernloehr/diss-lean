import NLS.SequenceSpaces.PeriodOneRealFormIdentity
import NLS.KdV.HillHminusOneDirichletLogNorming
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # One complex-ball hyperbolic-sine identity for native rough norming sequences -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem hillHminus_native_norming_sinh_identity
    (η : ℝ) (hη : 0 < η) (K S : PeriodOneHminusOne → Coeff 2)
    (hK : AnalyticOnNhd ℂ K (ball (0 : PeriodOneHminusOne) η))
    (hS : AnalyticOnNhd ℂ S (ball (0 : PeriodOneHminusOne) η))
    (hphysical : ∀ q ∈ ball (0 : PeriodOneHminusOne) η, ∀ hq : IsRealPeriodOneHminusOne q,
      ∀ n : ℕ+, K q (n : ℤ) = (hillHminusDirichletLogNorming q hq n : ℂ) ∧
        S q (n : ℤ) = (Real.sinh (hillHminusDirichletLogNorming q hq n) : ℂ))
    (hnonpos : ∀ q ∈ ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j ≤ 0 → K q j = 0 ∧ S q j = 0) :
    ∀ q ∈ ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, S q j = sinh (K q j) := by
  intro q hq j
  apply periodOneHminus_real_form_identity isOpen_ball (convex_ball (0 : PeriodOneHminusOne) η).isPreconnected
    (mem_ball_self hη) (fun p => S p j) (fun p => sinh (K p j))
    (fun p hp => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt _).comp (hS p hp))
    (fun p hp => by
      have hc := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).analyticAt _).comp (hK p hp)
      exact (hc.cexp.sub hc.neg.cexp).div_const)
    (fun p hp hJp => by
      have hpr := (periodOneHminusConjugation_fixed_iff p).mp hJp
      by_cases hj : 0 < j
      · let n : ℕ+ := ⟨j.toNat,by omega⟩
        have he : j = (n : ℤ) := by
          change j = (j.toNat : ℤ)
          exact (Int.toNat_of_nonneg hj.le).symm
        rw [he,(hphysical p hp hpr n).1,(hphysical p hp hpr n).2]
        exact Complex.ofReal_sinh _
      · obtain ⟨hK0,hS0⟩ := hnonpos p hp j (not_lt.mp hj)
        rw [hK0,hS0,sinh_zero]) hq

end NLS.KdV
