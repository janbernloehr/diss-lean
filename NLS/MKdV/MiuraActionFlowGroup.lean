import NLS.MKdV.MiuraActionFlowSobolev
import NLS.MKdV.MiuraGardnerTransfer

/-! # The complete physical Gardner action group

The Sobolev trajectories have the exact time law, commute, and have
period two pi. On every original real H1 input their actual L2 time
derivative is the Gardner derivative of the physical action J_n.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraActionInitialSource_injective (s : ℕ) (a b : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hb : ∀ j, b.val j = conj (b.val (-j)))
    (h : miuraActionInitialSource s a ha = miuraActionInitialSource s b hb) : a = b := by
  apply Subtype.ext
  funext j
  have he := congrArg (fun φ : realTypeSourceSubmodule 2 => φ.val.fst j) h
  simpa only [miuraActionInitialSource_fst] using he

@[simp] theorem miuraActionFlow_zero (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) : miuraActionFlow s a ha n 0 = a := by
  apply miuraActionInitialSource_injective s _ _ (miuraActionFlow_real s a ha n 0) ha
  rw [miuraActionFlow_source,miuraActionFlowFamily.data.hilbertPairedActionFlow_zero]

theorem miuraActionFlow_add (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t u : ℝ) :
    miuraActionFlow s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t) n u =
      miuraActionFlow s a ha n (t+u) := by
  apply miuraActionInitialSource_injective s _ _
    (miuraActionFlow_real s _ _ n u) (miuraActionFlow_real s a ha n (t+u))
  rw [miuraActionFlow_source,miuraActionFlow_source,miuraActionFlow_source,
    miuraActionFlowFamily.data.hilbertPairedActionFlow_add]

theorem miuraActionFlow_comm (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (t u : ℝ) :
    miuraActionFlow s (miuraActionFlow s a ha m t) (miuraActionFlow_real s a ha m t) n u =
      miuraActionFlow s (miuraActionFlow s a ha n u) (miuraActionFlow_real s a ha n u) m t := by
  apply miuraActionInitialSource_injective s _ _
    (miuraActionFlow_real s _ _ n u) (miuraActionFlow_real s _ _ m t)
  simp only [miuraActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_comm _ _ _ _ _ t u

theorem miuraActionFlow_periodic (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) :
    Function.Periodic (miuraActionFlow s a ha n) (2*Real.pi) := by
  intro t
  apply miuraActionInitialSource_injective s _ _
    (miuraActionFlow_real s a ha n (t+2*Real.pi)) (miuraActionFlow_real s a ha n t)
  simp only [miuraActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_periodic _ _ _ t

/-- The exact coefficient-preserving isometry between the established
H1 scalar domain and integer Sobolev order one. -/
def miuraH1SobolevEquiv : ScalarDomain 2 ≃ₗᵢ[ℂ] ScalarSobolev 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).trans
    (WeightedCoeff.weightIsometry (Weight.sobolev ((1 : ℕ) : ℝ)) 2).symm

theorem miuraH1SobolevEquiv_apply (a : ScalarDomain 2) (j : ℤ) :
    (miuraH1SobolevEquiv a).val j = a.val j := by
  change ((Weight.sobolev 1 j : ℂ)*a.val j)/(Weight.sobolev ((1 : ℕ) : ℝ) j : ℂ) = _
  rw [Nat.cast_one]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev 1) j)

theorem miuraH1SobolevEquiv_symm_apply (a : ScalarSobolev 1) (j : ℤ) :
    (miuraH1SobolevEquiv.symm a).val j = a.val j := by
  have h := miuraH1SobolevEquiv_apply (miuraH1SobolevEquiv.symm a) j
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

theorem miuraH1SobolevReal (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∀ j, (miuraH1SobolevEquiv a).val j = conj ((miuraH1SobolevEquiv a).val (-j)) := by
  intro j
  rw [miuraH1SobolevEquiv_apply,miuraH1SobolevEquiv_apply]
  exact ha j

theorem miuraActionInitialSource_one (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraActionInitialSource 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) = realDiagonalH1Source a ha := by
  apply Subtype.ext
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext j
    change (miuraActionInitialSource 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha)).val.fst j =
      (sobolevSourceInclusion (a,a)).fst j
    rw [miuraActionInitialSource_fst,miuraH1SobolevEquiv_apply,sobolevSourceInclusion_fst]
  · ext j
    change (miuraActionInitialSource 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha)).val.snd j =
      (sobolevSourceInclusion (a,a)).snd j
    rw [miuraActionInitialSource_snd,miuraH1SobolevEquiv_apply,sobolevSourceInclusion_snd]

def miuraH1ActionFlow (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (t : ℝ) : ScalarDomain 2 :=
  miuraH1SobolevEquiv.symm (miuraActionFlow 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) n t)

theorem miuraH1ActionFlow_coefficient (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) (j : ℤ) :
    (miuraH1ActionFlow a ha n t).val j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (realDiagonalH1Source a ha) n (-(n : ℤ)) t).val.fst j := by
  rw [miuraH1ActionFlow,miuraH1SobolevEquiv_symm_apply,miuraActionFlow_coefficient,miuraActionInitialSource_one]

theorem miuraH1ActionFlow_real (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    ∀ j, (miuraH1ActionFlow a ha n t).val j = conj ((miuraH1ActionFlow a ha n t).val (-j)) := by
  intro j
  simp only [miuraH1ActionFlow,miuraH1SobolevEquiv_symm_apply]
  exact miuraActionFlow_real 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) n t j

theorem miuraH1ActionFlow_source (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    realDiagonalH1Source (miuraH1ActionFlow a ha n t) (miuraH1ActionFlow_real a ha n t) =
      miuraActionFlowFamily.data.hilbertPairedActionFlow (realDiagonalH1Source a ha) n (-(n : ℤ)) t := by
  apply Subtype.ext
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext j
    change (sobolevSourceInclusion (miuraH1ActionFlow a ha n t,miuraH1ActionFlow a ha n t)).fst j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (realDiagonalH1Source a ha) n (-(n : ℤ)) t).val.fst j
    rw [sobolevSourceInclusion_fst,miuraH1ActionFlow_coefficient]
  · ext j
    change (sobolevSourceInclusion (miuraH1ActionFlow a ha n t,miuraH1ActionFlow a ha n t)).snd j =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (realDiagonalH1Source a ha) n (-(n : ℤ)) t).val.snd j
    rw [sobolevSourceInclusion_snd,miuraH1ActionFlow_coefficient]
    exact congrArg (fun b : Coeff 2 => b j) (miuraActionFlowFamily.data.hilbertPairedActionFlow_diagonal
      (realDiagonalH1Source a ha) rfl n t)

theorem realDiagonalH1Source_injective (a b : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hb : ∀ j, b.val j = conj (b.val (-j)))
    (h : realDiagonalH1Source a ha = realDiagonalH1Source b hb) : a = b := by
  apply Subtype.ext
  funext j
  have he := congrArg (fun φ : realTypeSourceSubmodule 2 => φ.val.fst j) h
  change (sobolevSourceInclusion (a,a)).fst j = (sobolevSourceInclusion (b,b)).fst j at he
  simpa only [sobolevSourceInclusion_fst] using he

@[simp] theorem miuraH1ActionFlow_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) : miuraH1ActionFlow a ha n 0 = a := by
  apply realDiagonalH1Source_injective _ _ (miuraH1ActionFlow_real a ha n 0) ha
  rw [miuraH1ActionFlow_source,miuraActionFlowFamily.data.hilbertPairedActionFlow_zero]

theorem miuraH1ActionFlow_add (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t u : ℝ) :
    miuraH1ActionFlow (miuraH1ActionFlow a ha n t) (miuraH1ActionFlow_real a ha n t) n u =
      miuraH1ActionFlow a ha n (t+u) := by
  apply realDiagonalH1Source_injective _ _ (miuraH1ActionFlow_real _ _ n u) (miuraH1ActionFlow_real a ha n (t+u))
  simp only [miuraH1ActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_add _ _ _ t u

theorem miuraH1ActionFlow_comm (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (t u : ℝ) :
    miuraH1ActionFlow (miuraH1ActionFlow a ha m t) (miuraH1ActionFlow_real a ha m t) n u =
      miuraH1ActionFlow (miuraH1ActionFlow a ha n u) (miuraH1ActionFlow_real a ha n u) m t := by
  apply realDiagonalH1Source_injective _ _ (miuraH1ActionFlow_real _ _ n u) (miuraH1ActionFlow_real _ _ m t)
  simp only [miuraH1ActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_comm _ _ _ _ _ t u

theorem miuraH1ActionFlow_periodic (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) :
    Function.Periodic (miuraH1ActionFlow a ha n) (2*Real.pi) := by
  intro t
  apply realDiagonalH1Source_injective _ _
    (miuraH1ActionFlow_real a ha n (t+2*Real.pi)) (miuraH1ActionFlow_real a ha n t)
  simp only [miuraH1ActionFlow_source]
  exact miuraActionFlowFamily.data.hilbertPairedActionFlow_periodic _ _ _ t

theorem continuous_miuraH1ActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) : Continuous (miuraH1ActionFlow a ha n) :=
  miuraH1SobolevEquiv.symm.continuous.comp
    (continuous_miuraActionFlow 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) n)

theorem scalarInclusion_miuraH1ActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    scalarInclusion (miuraH1ActionFlow a ha n t) =
      (miuraActionFlowFamily.data.hilbertPairedActionFlow (realDiagonalH1Source a ha) n (-(n : ℤ)) t).val.fst := by
  ext j
  rw [scalarInclusion_apply,miuraH1ActionFlow_coefficient]

/-- The original H1 curve solves the actual Gardner equation at every
real time. The velocity is defined using the actual L2 Frechet gradient. -/
theorem hasDerivAt_miuraH1ActionFlow_Gardner (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (fun r => scalarInclusion (miuraH1ActionFlow a ha n r))
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion (miuraH1ActionFlow a ha n t))) t := by
  let D := miuraActionFlowFamily.data
  let φ := realDiagonalH1Source a ha
  let P : CoeffPair 2 →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).comp (CoeffPair.toMax 2).toContinuousLinearMap
  have hd := (P.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (D.hasDerivAt_hilbertPairedActionFlow φ n (-(n : ℤ)) t)
  change HasDerivAt (fun r => (D.hilbertPairedActionFlow φ n (-(n : ℤ)) r).val.fst)
    (sourceActionDifferenceVector n (-(n : ℤ)) (D.hilbertPairedActionFlow φ n (-(n : ℤ)) t).val).fst t at hd
  have hf : (fun r => (D.hilbertPairedActionFlow φ n (-(n : ℤ)) r).val.fst) =
      (fun r => scalarInclusion (miuraH1ActionFlow a ha n r)) :=
    funext (fun r => (scalarInclusion_miuraH1ActionFlow a ha n r).symm)
  rw [hf] at hd
  let b := miuraH1ActionFlow a ha n t
  have hb := miuraH1ActionFlow_real a ha n t
  have hs : (D.hilbertPairedActionFlow φ n (-(n : ℤ)) t).val = sobolevSourceInclusion (b,b) :=
    (congrArg Subtype.val (miuraH1ActionFlow_source a ha n t)).symm
  rw [hs] at hd
  have hv : sourceActionDifferenceVector n (-(n : ℤ)) (sobolevSourceInclusion (b,b)) =
      scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion b)) := by
    unfold sourceActionDifferenceVector sourceHamiltonianVector
    rw [← map_sub]
    exact miuraActionDifference_direction b hb n hn
  rw [hv,scalarL2Diagonal_fst] at hd
  exact hd

end NLS.MKdV
