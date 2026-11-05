import NLS.MKdV.MiuraActionFlowSobolev
import NLS.MKdV.MiuraSobolevActionSequence
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexAnalytic

/-! # Native weighted NLS coordinates along the scalar Sobolev diagonal

The original weighted Birkhoff map is pulled back by the actual scalar
diagonal, with every original Fourier coefficient retained. Its normalized
coordinate sequences have precisely the scalar Sobolev weight, on a common
complex neighborhood of every physical profile at every integer order.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSobolevNLSInput (s : ℕ) : ScalarSobolev s →L[ℂ]
    WeightedCoeffPair (sourceFrequencyWeight (miuraActionFlowWeight s)) 2 :=
  (WeightedCoeffPair.inlCLM _).comp (miuraActionWeightEquiv s).toContinuousLinearEquiv.toContinuousLinearMap+
    (WeightedCoeffPair.inrCLM _).comp (miuraActionWeightEquiv s).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem miuraSobolevNLSInput_fst (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (miuraSobolevNLSInput s a).fst.val j = a.val j := by
  change (miuraActionWeightEquiv s a).val j+0 = a.val j
  rw [add_zero,miuraActionWeightEquiv_apply]

@[simp] theorem miuraSobolevNLSInput_snd (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (miuraSobolevNLSInput s a).snd.val j = a.val j := by
  change 0+(miuraActionWeightEquiv s a).val j = a.val j
  rw [zero_add,miuraActionWeightEquiv_apply]

theorem miuraSobolevNLSInput_source (s : ℕ) (a : ScalarSobolev s) :
    originalWeightedSourceCLM (miuraActionFlowWeight s) (miuraSobolevNLSInput s a) = miuraSobolevActionSource s a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j
  · change (originalWeightedSourceCLM _ _).fst j = (miuraSobolevActionSource s a).fst j
    rw [originalWeightedSourceCLM_fst,miuraSobolevNLSInput_fst,miuraSobolevActionSource_fst]
  · change (originalWeightedSourceCLM _ _).snd j = (miuraSobolevActionSource s a).snd j
    rw [originalWeightedSourceCLM_snd,miuraSobolevNLSInput_snd,miuraSobolevActionSource_snd]

def miuraSobolevNLSNormalizedCoordinates (s : ℕ) (a : ScalarSobolev s) : Coeff 2 × Coeff 2 :=
  CoeffPair.toMax 2 (sourcePairWeightCoordinates (miuraActionFlowWeight s)
    (originalWeightedBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi
      (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)))

/-- One native complex domain carries the entire normalized coordinate
pair with its exact original scalar Sobolev weights at every index. -/
theorem exists_miuraSobolevNLSNormalizedCoordinates_domain (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧ {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraSobolevNLSNormalizedCoordinates s) U ∧
      ∀ b ∈ U, ∀ n : ℤ,
        (miuraSobolevNLSNormalizedCoordinates s b).1 n = (Weight.sobolev (s : ℝ) n : ℂ)*
          (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (miuraSobolevActionSource s b)).1 n ∧
        (miuraSobolevNLSNormalizedCoordinates s b).2 n = (Weight.sobolev (s : ℝ) n : ℂ)*
          (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (miuraSobolevActionSource s b)).2 n := by
  let D := miuraActionFlowFamily.data
  obtain ⟨V,hV,hreal,_,hAn,hcoord⟩ := D.exists_originalWeightedBirkhoffMap_analytic (miuraActionFlowWeight s)
  let U := miuraSobolevNLSInput s ⁻¹' V
  let T := (CoeffPair.toMax 2).toContinuousLinearMap.comp
    (sourcePairWeightCoordinates (miuraActionFlowWeight s)).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨U,hV.preimage (miuraSobolevNLSInput s).continuous,?_,?_,?_⟩
  · intro a ha
    have hm : miuraSobolevNLSInput s a ∈ weightedRealSourceSubmodule (miuraActionFlowWeight s) := by
      apply (mem_weightedRealSourceSubmodule_iff _ _).mpr
      intro j
      rw [miuraSobolevNLSInput_snd,miuraSobolevNLSInput_fst]
      exact ha j
    exact hreal ⟨miuraSobolevNLSInput s a,hm⟩
  · intro b hb
    exact (T.analyticAt _).comp ((hAn _ hb).comp ((miuraSobolevNLSInput s).analyticAt b))
  · intro b hb n
    have hc := hcoord _ hb n
    constructor
    · change (miuraActionFlowWeight s (2*n) : ℂ)*
        (originalWeightedBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi
          (miuraActionFlowWeight s) (miuraSobolevNLSInput s b)).fst.val n = _
      rw [hc.1,miuraSobolevNLSInput_source,miuraActionFlowWeight,sourceSobolevSpectralWeight_even]
    · change (miuraActionFlowWeight s (2*n) : ℂ)*
        (originalWeightedBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi
          (miuraActionFlowWeight s) (miuraSobolevNLSInput s b)).snd.val n = _
      rw [hc.2,miuraSobolevNLSInput_source,miuraActionFlowWeight,sourceSobolevSpectralWeight_even]

end NLS.MKdV
