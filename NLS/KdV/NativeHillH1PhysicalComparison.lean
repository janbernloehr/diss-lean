import NLS.KdV.NativeHillSourceComparisons
import NLS.KdV.HillNativeH1Source
import NLS.KdV.HillWeightedNativeSource
import NLS.KdV.NativeHamiltonianPhysicalIntegrals

/-! Exact comparison of the original native H1 source with the weighted
physical H1 source used by the Hilbert-action Hamiltonian extension. The
bounded change of weight preserves EVERY coefficient and physical energy. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.Fourier
open scoped ComplexConjugate
namespace NLS.KdV

def nativeToHillH1 : ScalarSobolev 1 →L[ℂ] HillNativeH1 :=
  WeightedCoeff.weightedMultiplierCLM (Weight.sobolev ((1 : ℕ) : ℝ)) hillH1SpectralWeight.doubleIndex.toWeight
    (fun _ => 1) 2 (by norm_num) (by
      intro j
      rw [hillH1SpectralWeight_doubleIndex]
      simp only [norm_one,mul_one,Weight.sobolev_apply,Nat.cast_one,Real.rpow_one]
      linarith [abs_nonneg (j : ℝ)])

@[simp] theorem nativeToHillH1_coefficient (q : ScalarSobolev 1) (j : ℤ) :
    (nativeToHillH1 q).val j=q.val j := one_mul _

def nativeRealHillH1 (q : ScalarSobolev 1) (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    RealHillWeightedPotential hillH1SpectralWeight :=
  ⟨nativeToHillH1 q,by intro j;simpa only [SpectralWeight.toCoeff_apply,nativeToHillH1_coefficient] using hq j⟩

/-- The entire rough source is unchanged by the native physical comparison. -/
theorem nativeToHillH1_rough (q : ScalarSobolev 1) :
    hillWeightedNativeHminusSource hillH1SpectralWeight (nativeToHillH1 q)=nativeHillSource 1 q := by
  apply Subtype.ext
  funext j
  simp only [hillWeightedNativeHminusSource_apply,nativeToHillH1_coefficient,nativeHillSource_apply]

/-- Both canonical continuous physical representatives agree everywhere. -/
theorem nativeToHillH1_continuous (q : ScalarSobolev 1) :
    hillNativeH1Continuous (nativeToHillH1 q)=nativeHillContinuousSource 1 (by decide) q := by
  have he : hillNativeH1ToSobolev (nativeToHillH1 q)=hierarchySobolevToScalarDomain 1 (by decide) q := by
    apply Subtype.ext
    funext j
    simp only [hillNativeH1ToSobolev_apply,nativeToHillH1_coefficient,hierarchySobolevToScalarDomain_apply]
  exact congrArg periodOneSobolevSynthesis he

/-- The independent physical H1 Hamiltonians are EXACTLY equal, with no
smoothness premise and no change of unit period or coefficients. -/
theorem nativeToHillH1_hamiltonian (q : ScalarSobolev 1) :
    hillNativeH1Hamiltonian (nativeToHillH1 q)=nativeKdVHamiltonian q := by
  rw [hillNativeH1Hamiltonian_eq_physical_integral,nativeToHillH1_continuous]
  simpa only [nativeHillContinuousSource_eq_zero_jet] using (nativeKdVHamiltonian_eq_classical q).symm

/-- The literal original even physical Hill sources agree, including all
labels and original action integrals. -/
theorem nativeRealHillH1_physical (q : ScalarSobolev 1) (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    hillWeightedPhysicalSource hillH1SpectralWeight (nativeRealHillH1 q hq)=nativeHillPhysicalSource 1 q hq := by
  apply Subtype.ext
  have he := congrArg hillContinuousCoefficients (nativeToHillH1_continuous q)
  rw [hillContinuousCoefficients_hillNativeH1Continuous,
    hillContinuousCoefficients_nativeHillContinuousSource 1 (by decide) q hq] at he
  exact he

end NLS.KdV
