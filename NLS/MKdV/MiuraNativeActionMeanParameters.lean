import NLS.MKdV.MiuraSobolevNormalizedActionFlow
import NLS.MKdV.MiuraCartesianActionParameters

/-! # Native physical actions and signed mean under Cartesian normalization

The native action topology is weight 2s+1 in l1. Normalization is a bounded
linear equivalence; the signed mean is retained literally and linearly.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraNativeActionMeanTarget (s : ℕ) := WeightedCoeff (miuraSpectralActionWeight s) 1 × ℂ

def miuraNativeActionMeanEquiv (s : ℕ) : MiuraNativeActionMeanTarget s ≃L[ℂ] MiuraActionMeanTarget :=
  (((WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).toContinuousLinearEquiv.trans
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm.toContinuousLinearEquiv).prodCongr
      (ContinuousLinearEquiv.refl ℂ ℂ))

def miuraNativeActionMeanMap (s : ℕ) (a : ScalarSobolev s) : MiuraNativeActionMeanTarget s :=
  (miuraSobolevActionSequence s a,a.val 0)

def miuraNormalizedNativeActionMeanMap (s : ℕ) (a : ScalarSobolev s) : MiuraActionMeanTarget :=
  miuraNativeActionMeanEquiv s (miuraNativeActionMeanMap s a)

theorem miuraNativeActionMeanEquiv_fst (s : ℕ) (b : MiuraNativeActionMeanTarget s) (n : ℤ) :
    (miuraNativeActionMeanEquiv s b).1.val n =
      ((miuraSpectralActionWeight s n : ℂ)*b.1.val n)/(Weight.sobolev 1 n : ℂ) := rfl

theorem miuraNativeActionMeanEquiv_mean (s : ℕ) (b : MiuraNativeActionMeanTarget s) :
    (miuraNativeActionMeanEquiv s b).2 = b.2 :=
  NLS.FunctionalAnalysis.prodCongr_refl_snd
    ((WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).toContinuousLinearEquiv.trans
      (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm.toContinuousLinearEquiv) b

theorem miuraSobolevActionWeight_normalization (s : ℕ) (n : ℤ) :
    Weight.sobolev 1 n*(Weight.sobolev (s : ℝ) n)^2 = miuraSpectralActionWeight s n := by
  have hhalf : Weight.sobolev (1/2) n*Weight.sobolev (1/2) n = Weight.sobolev 1 n := by
    rw [Weight.sobolev_apply,← Real.rpow_add (by positivity)]
    norm_num
  calc
    _ = (Weight.sobolev (s : ℝ) n*Weight.sobolev (1/2) n)*
        (Weight.sobolev (s : ℝ) n*Weight.sobolev (1/2) n) := by rw [← hhalf]; ring
    _ = _ := by rw [← miuraCartesianWeight_factor,miuraCartesianWeight_squared]

/-- The normalized Cartesian radii are exactly the original physical
actions, transported from their full native topology, and signed mean. -/
theorem miuraNormalizedCartesian_actionMean (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraPositiveCartesianActionMean (miuraSobolevNormalizedCartesianMap s a) =
      miuraNormalizedNativeActionMeanMap s a := by
  apply Prod.ext
  · apply (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).injective
    ext n
    change (Weight.sobolev 1 n : ℂ)*
        (miuraPositiveCartesianActionMean (miuraSobolevNormalizedCartesianMap s a)).1.val n =
      (Weight.sobolev 1 n : ℂ)*(miuraNativeActionMeanEquiv s (miuraNativeActionMeanMap s a)).1.val n
    rw [miuraNativeActionMeanEquiv_fst,mul_div_cancel₀ _ ((Weight.sobolev 1).complex_ne_zero n)]
    by_cases hn : 0 < n
    · have he := (miuraSobolevNormalizedCartesianMap_eval s a n).trans
        (congrArg (fun z : ℂ × ℂ => (Weight.sobolev (s : ℝ) n : ℂ) • z)
          (miuraSobolevPositiveCartesianMap_eval_sequence s a n hn))
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (miuraSobolevNormalizedCartesianMap s a).1.1.val.val n =
        (Weight.sobolev (s : ℝ) n : ℂ)*(miuraSobolevCartesianSequence s a).1.val n at hx
      change (miuraSobolevNormalizedCartesianMap s a).1.2.val.val n =
        (Weight.sobolev (s : ℝ) n : ℂ)*(miuraSobolevCartesianSequence s a).2.val n at hy
      have hr := congrArg (fun J : WeightedCoeff (miuraSpectralActionWeight s) 1 => J.val n)
        (miuraSobolevCartesianActions_sequence_eq s a ha)
      rw [miuraSobolevCartesianActions_apply] at hr
      change (Weight.sobolev 1 n : ℂ)*
        (miuraL2CartesianActions ((miuraSobolevNormalizedCartesianMap s a).1.1.val,
          (miuraSobolevNormalizedCartesianMap s a).1.2.val)).val n =
        (miuraSpectralActionWeight s n : ℂ)*(miuraSobolevActionSequence s a).val n
      rw [miuraL2CartesianActions_apply,hx,hy,← hr]
      have hw : (Weight.sobolev 1 n : ℂ)*(Weight.sobolev (s : ℝ) n : ℂ)^2 =
          (miuraSpectralActionWeight s n : ℂ) := by exact_mod_cast miuraSobolevActionWeight_normalization s n
      linear_combination ((miuraSobolevCartesianSequence s a).1.val n^2+
        (miuraSobolevCartesianSequence s a).2.val n^2)/2*hw
    · change (Weight.sobolev 1 n : ℂ)*
        (miuraL2CartesianActions ((miuraSobolevNormalizedCartesianMap s a).1.1.val,
          (miuraSobolevNormalizedCartesianMap s a).1.2.val)).val n =
        (miuraSpectralActionWeight s n : ℂ)*(miuraSobolevActionSequence s a).val n
      rw [miuraL2CartesianActions_apply,(miuraSobolevNormalizedCartesianMap s a).1.1.property n (by omega),
        (miuraSobolevNormalizedCartesianMap s a).1.2.property n (by omega),
        miuraSobolevActionSequence_nonpositive s a n hn]
      ring
  · exact miuraSobolevNormalizedCartesianMap_mean s a

end NLS.MKdV
