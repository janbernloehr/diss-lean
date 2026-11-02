import NLS.ZakharovShabat.SourceWeightedPairedActionFlow
import NLS.MKdV.MiuraL2Actions
import NLS.ZakharovShabat.SobolevPhysicalJets

/-! # Complete physical mKdV action trajectories in native Sobolev norms

Opposite original NLS action rotations preserve the actual real diagonal.
The native weighted inverse constructs their scalar lifts on every H^s,
s>=0, continuously in time in that full Sobolev norm. Every original raw
Fourier coefficient is retained when weights are forgotten.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraActionFlowFamily where
  base : Set (CoeffPair 2)
  beta : Set (CoeffPair 2)
  domain : Set (CoeffPair 2)
  psi : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n
  data : SourceBirkhoffMapComplexData (by simp) (by norm_num) base beta domain psi

theorem nonempty_miuraActionFlowFamily : Nonempty MiuraActionFlowFamily := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨⟨W₀,B,W,s,D⟩⟩

def miuraActionFlowFamily : MiuraActionFlowFamily := Classical.choice nonempty_miuraActionFlowFamily

def miuraActionFlowWeight (s : ℕ) : SpectralWeight := sourceSobolevSpectralWeight s (Nat.cast_nonneg s)

def miuraActionWeightEquiv (s : ℕ) :
    ScalarSobolev s ≃ₗᵢ[ℂ] WeightedCoeff (sourceFrequencyWeight (miuraActionFlowWeight s)) 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (s : ℝ)) 2).trans
    (WeightedCoeff.weightIsometry (sourceFrequencyWeight (miuraActionFlowWeight s)) 2).symm

theorem miuraActionWeightEquiv_apply (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (miuraActionWeightEquiv s a).val j = a.val j := by
  change ((Weight.sobolev (s : ℝ) j : ℂ)*a.val j)/((miuraActionFlowWeight s) (2*j) : ℂ) = _
  rw [miuraActionFlowWeight,sourceSobolevSpectralWeight_even]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev (s : ℝ)) j)

def miuraActionWeightedSource (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    weightedRealSourceSubmodule (p := 2) (miuraActionFlowWeight s) :=
  ⟨WithLp.toLp 2 (miuraActionWeightEquiv s a,miuraActionWeightEquiv s a),
    (mem_weightedRealSourceSubmodule_iff _ _).mpr (by
      intro j
      change (miuraActionWeightEquiv s a).val j = conj ((miuraActionWeightEquiv s a).val (-j))
      rw [miuraActionWeightEquiv_apply,miuraActionWeightEquiv_apply]
      exact ha j)⟩

def miuraActionInitialSource (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : realTypeSourceSubmodule 2 :=
  originalWeightedRealSource (miuraActionFlowWeight s) (miuraActionWeightedSource s a ha)

@[simp] theorem miuraActionInitialSource_fst (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (j : ℤ) :
    (miuraActionInitialSource s a ha).val.fst j = a.val j := by
  rw [miuraActionInitialSource,originalWeightedRealSource_fst]
  exact miuraActionWeightEquiv_apply s a j

@[simp] theorem miuraActionInitialSource_snd (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (j : ℤ) :
    (miuraActionInitialSource s a ha).val.snd j = a.val j := by
  rw [miuraActionInitialSource,originalWeightedRealSource_snd]
  exact miuraActionWeightEquiv_apply s a j

theorem miuraActionInitialSource_diagonal (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (miuraActionInitialSource s a ha).val.fst = (miuraActionInitialSource s a ha).val.snd := by
  ext j
  rw [miuraActionInitialSource_fst,miuraActionInitialSource_snd]

def miuraActionScalarProjection (s : ℕ) :
    WeightedCoeffPair (sourceFrequencyWeight (miuraActionFlowWeight s)) 2 →L[ℂ] ScalarSobolev s :=
  (miuraActionWeightEquiv s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)

theorem miuraActionScalarProjection_apply (s : ℕ)
    (b : WeightedCoeffPair (sourceFrequencyWeight (miuraActionFlowWeight s)) 2) (j : ℤ) :
    (miuraActionScalarProjection s b).val j = b.fst.val j := by
  change ((miuraActionWeightEquiv s).symm b.fst).val j = _
  have h := miuraActionWeightEquiv_apply s ((miuraActionWeightEquiv s).symm b.fst) j
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

def miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) : ScalarSobolev s :=
  miuraActionScalarProjection s
    (miuraActionFlowFamily.data.weightedPairedActionFlow s (Nat.cast_nonneg s)
      (miuraActionWeightedSource s a ha) n (-(n : ℤ)) t).val

theorem miuraActionFlow_coefficient (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) (j : ℤ) :
    (miuraActionFlow s a ha n t).val j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (miuraActionInitialSource s a ha) n (-(n : ℤ)) t).val.fst j := by
  rw [miuraActionFlow]
  erw [miuraActionScalarProjection_apply]
  have h := congrArg (fun b : realTypeSourceSubmodule 2 => b.val.fst j)
    (miuraActionFlowFamily.data.originalWeightedRealSource_pairedActionFlow s (Nat.cast_nonneg s)
      (miuraActionWeightedSource s a ha) n (-(n : ℤ)) t)
  rw [originalWeightedRealSource_fst] at h
  exact h

theorem miuraActionFlow_real (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    ∀ j, (miuraActionFlow s a ha n t).val j = conj ((miuraActionFlow s a ha n t).val (-j)) := by
  intro j
  rw [miuraActionFlow_coefficient,miuraActionFlow_coefficient]
  let φ := miuraActionInitialSource s a ha
  let χ := miuraActionFlowFamily.data.hilbertPairedActionFlow φ n (-(n : ℤ)) t
  have h := χ.property j
  change χ.val.snd j = conj (χ.val.fst (-j)) at h
  rw [← miuraActionFlowFamily.data.hilbertPairedActionFlow_diagonal φ
    (miuraActionInitialSource_diagonal s a ha) n t] at h
  exact h

theorem miuraActionFlow_source (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraActionInitialSource s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t) =
      miuraActionFlowFamily.data.hilbertPairedActionFlow (miuraActionInitialSource s a ha) n (-(n : ℤ)) t := by
  apply Subtype.ext
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext j
    change (miuraActionInitialSource s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t)).val.fst j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (miuraActionInitialSource s a ha) n (-(n : ℤ)) t).val.fst j
    rw [miuraActionInitialSource_fst,miuraActionFlow_coefficient]
  · ext j
    change (miuraActionInitialSource s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t)).val.snd j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (miuraActionInitialSource s a ha) n (-(n : ℤ)) t).val.snd j
    rw [miuraActionInitialSource_snd,miuraActionFlow_coefficient]
    exact congrArg (fun b : Coeff 2 => b j) (miuraActionFlowFamily.data.hilbertPairedActionFlow_diagonal
      (miuraActionInitialSource s a ha) (miuraActionInitialSource_diagonal s a ha) n t)

/-- The trajectory is continuous in the full native H^s norm. -/
theorem continuous_miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) :
    Continuous (miuraActionFlow s a ha n) := by
  let w := sourceSobolevSpectralWeight (s : ℝ) (Nat.cast_nonneg s)
  let b : weightedRealSourceSubmodule (p := 2) w := miuraActionWeightedSource s a ha
  have hp : Continuous (fun t : ℝ => (t,b)) := continuous_id.prodMk continuous_const
  have hc := (miuraActionFlowFamily.data.continuous_weightedPairedActionFlow s
    (Nat.cast_nonneg s) n (-(n : ℤ))).comp hp
  have hv := (weightedRealSourceSubmodule (p := 2) w).subtypeL.continuous.comp hc
  exact (miuraActionScalarProjection s).continuous.comp hv

end NLS.MKdV
