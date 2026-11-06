import NLS.KdV.HillHminusOneCriticalPoints
import NLS.SequenceSpaces.PeriodOneRealMiuraCharts

/-! # Real rough Hill charts with actual real-type diagonal sources

The actual complex Miura chart preserves physical realness on its real
slice. The resulting diagonal NLS source is proved real type there.
-/
noncomputable section
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillMiuraDiagonal_isRealType (a : Coeff 2)
    (ha : periodOneL2Conjugation a = a) :
    IsRealType (CoeffPair.toMax 2 (hillMiuraDiagonal a)) := by
  intro k
  change (hillMiuraDiagonal a).snd k = conj ((hillMiuraDiagonal a).fst (-k))
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]
  exact (congrArg (fun b : Coeff 2 => b k) ha).symm

/-- Every real Hminus1 potential has a constructed actual analytic chart
with a fixed positive real energy translation. All real inputs in its
domain have real lifts and real-type diagonal spectral sources. -/
theorem exists_real_hillHminusMiuraChart (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, q0 ∈ C.domain ∧ 0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
      ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
        periodOneL2Conjugation (C.lift q) = C.lift q ∧
          IsRealType (CoeffPair.toMax 2 (C.criticalSource q)) := by
  obtain ⟨m,U,hU,hq,u,hu,himage,hreal⟩ := exists_real_periodOneMiura_energyChart q0 hq0
  let C : HillHminusMiuraChart := {
    domain := U, domain_open := hU, energyShift := (((m : ℝ)+1 : ℝ)/2 : ℂ)^2,
    lift := u, lift_analytic := hu, image := himage }
  have hshift : C.energyShift = (((((m : ℝ)+1)/2 : ℝ) : ℂ)^2) := by
    simp only [C,ofReal_div,ofReal_ofNat]
  refine ⟨C,hq,?_,?_,?_⟩
  · rw [hshift,← ofReal_pow,ofReal_re]
    positivity
  · rw [hshift,← ofReal_pow,ofReal_im]
  · intro q hq hqr
    have hr := hreal q hq hqr
    exact ⟨hr,hillMiuraDiagonal_isRealType (u q) hr⟩

end NLS.KdV
