import NLS.KdV.HillDirichletNormingData
import NLS.SequenceSpaces.WeightedFiniteCoefficients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

def hillPeriodOneTruncateValue (N : ℕ) (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  q-WeightedCoeff.fourierTail (p := 2) SpectralWeight.one.toWeight N q

theorem hillPeriodOneTruncateValue_apply (N : ℕ) (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (hillPeriodOneTruncateValue N q).val k=if k.natAbs<N then q.val k else 0 := by
  change q.val k-(WeightedCoeff.fourierTail (p := 2) SpectralWeight.one.toWeight N q).val k=_
  rw [WeightedCoeff.fourierTail_apply]
  by_cases hk : k.natAbs<N <;> simp [hk,Nat.not_le_of_lt,Nat.le_of_not_gt]

def hillRealPeriodOneTruncate (N : ℕ) (q : RealPeriodOneHillPotential) : RealPeriodOneHillPotential :=
  ⟨hillPeriodOneTruncateValue N q.val,by
    constructor
    · rw [Coeff.mem_paritySubspace]
      intro k hk
      simp only [SpectralWeight.toCoeff_apply,hillPeriodOneTruncateValue_apply]
      split_ifs
      · simpa only [SpectralWeight.toCoeff_apply] using (Coeff.mem_paritySubspace 0 _).mp q.property.1 k hk
      · rfl
    · intro k
      simp only [SpectralWeight.toCoeff_apply,hillPeriodOneTruncateValue_apply,Int.natAbs_neg]
      have hr : q.val.val (-k)=conj (q.val.val k) := by
        simpa only [SpectralWeight.toCoeff_apply] using q.property.2 k
      by_cases hk : k.natAbs<N <;> simp [hk,hr]⟩

theorem tendsto_hillRealPeriodOneTruncate (q : RealPeriodOneHillPotential) :
    Tendsto (fun N : ℕ => hillRealPeriodOneTruncate N q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  have hh := (tendsto_const_nhds (x := q.val)).sub
    (WeightedCoeff.tendsto_fourierTail (p := 2) (by norm_num) SpectralWeight.one.toWeight q.val)
  simpa only [hillRealPeriodOneTruncate,hillPeriodOneTruncateValue,sub_zero] using hh

def hillRealPeriodOneTruncationFinsupp (N : ℕ) (q : RealPeriodOneHillPotential) : ℤ →₀ ℂ :=
  Finsupp.onFinset (Coeff.lowFrequencies N) (hillRealPeriodOneTruncate N q).val.val (by
    intro k hk
    by_contra hn
    apply hk
    change (hillPeriodOneTruncateValue N q.val).val k=0
    rw [hillPeriodOneTruncateValue_apply]
    simp only [Coeff.mem_lowFrequencies] at hn
    exact if_neg hn)

theorem hillContinuousCoefficients_realPeriodOneTruncation (N : ℕ) (q : RealPeriodOneHillPotential) :
    hillContinuousCoefficients
      (Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q)))=
        (hillRealPeriodOneTruncate N q).val := by
  apply Subtype.ext
  funext k
  rw [hillContinuousCoefficients_apply,Fourier.fourierCoeff_continuousSynthesis]
  rfl

end NLS.KdV
