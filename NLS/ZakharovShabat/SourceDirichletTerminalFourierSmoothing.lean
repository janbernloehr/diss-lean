import NLS.ZakharovShabat.SourceEtaMidpointFourierAnalytic
import NLS.ZakharovShabat.SourceEtaSineFourierAnalytic
import NLS.ZakharovShabat.SourceDirichletTerminalJacobianCompact

/-! One-smoothing for the literal Dirichlet terminal coordinate itself.
The exact midpoint and sine Fourier remainders give the result directly,
with all labels, both signs and collapsed gaps retained. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceGapWeightedEtaTerminal_fourier_decomposition
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (sign : ℂ) (n : ℤ) :
    sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ -
      sourceGapWeightedEtaTerminalFourier sign ψ n =
        -2 * sourceEtaMidpointFourierError hp hp1 ψ n -
          (2 * sign * I) * sourceEtaSineFourierError hp hp1 ψ n := by
  simp only [sourceGapWeightedEtaTerminalCoordinate,
    sourceGapWeightedEtaTerminalFourier_apply, sourceEtaMidpointFourierError,
    sourceEtaSineFourierError, sourceDirichletMidpointDisplacement_apply,
    sourceStandardRootMidpoint]
  ring_nf
  simp only [I_sq]
  ring

def sourceTerminalFourierRemainder (m : ℕ) (sign : ℂ) (b : SobolevSource m) :
    WeightedCoeff (Weight.sobolev ((m : ℝ) + 1)) 2 :=
  (-2 : ℂ) • sourceEtaMidpointFourierRemainder m b -
    (2 * sign * I) • sourceEtaSineFourierRemainder m b

theorem exists_local_sourceTerminalFourierRemainder_analytic
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧ a.val ∈ U ∧
      ∀ sign : ℂ, AnalyticOnNhd ℂ (sourceTerminalFourierRemainder m sign) U ∧
        ∀ b ∈ U, ∀ n : ℤ, (sourceTerminalFourierRemainder m sign b).val n =
          sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n sign
            (higherSobolevSourceInclusion m b) -
              sourceGapWeightedEtaTerminalFourier sign (higherSobolevSourceInclusion m b) n := by
  obtain ⟨Va,hVa,haVa,_,_,hAa,hAc⟩ :=
    exists_local_sourceEtaMidpointFourierRemainder_analytic m hm a
  obtain ⟨Vb,hVb,haVb,_,_,hBa,hBc⟩ :=
    exists_local_sourceEtaSineFourierRemainder_analytic m hm a
  refine ⟨Va ∩ Vb,hVa.inter hVb,⟨haVa,haVb⟩,fun sign => ⟨?_,?_⟩⟩
  · intro b hb
    exact ((hAa b hb.1).const_smul (c := (-2 : ℂ))).sub
      ((hBa b hb.2).const_smul (c := 2 * sign * I))
  · intro b hb n
    rw [sourceGapWeightedEtaTerminal_fourier_decomposition]
    simp only [sourceTerminalFourierRemainder, WeightedCoeff.sub_val, WeightedCoeff.smul_val,
      (hAc b hb.1).2 n, (hBc b hb.2).2 n]

end NLS.ZakharovShabat
