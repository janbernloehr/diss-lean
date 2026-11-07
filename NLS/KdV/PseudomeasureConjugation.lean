import NLS.KdV.PseudomeasureCoefficients
import NLS.KdV.PseudomeasureBilinearSymmetry
import NLS.SequenceSpaces.ConjugateReflection

/-! Physical conjugation of the actual endpoint Fourier tail inverse and
effective Hill coefficients, including the full singular endpoint carrier. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- Physical Fourier conjugation retains every source spectral weight. -/
def endpointConjugate (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) : WeightedCoeff (w.negativeSobolev r) ⊤ :=
  WeightedCoeff.conjugateReflection _ (w.negativeSobolev_neg r) q

@[simp] theorem endpointConjugate_apply (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointConjugate w r q).val k = (starRingEnd ℂ) (q.val (-k)) :=
  WeightedCoeff.conjugateReflection_apply _ _ q k

@[simp] theorem norm_endpointConjugate (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) : ‖endpointConjugate w r q‖ = ‖q‖ :=
  WeightedCoeff.norm_conjugateReflection _ _ q

@[simp] theorem endpointConjugate_involutive (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointConjugate w r (endpointConjugate w r q) = q :=
  WeightedCoeff.conjugateReflection_involutive _ _ q

theorem endpointConjugate_sub (w : SpectralWeight) (r : ℝ)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointConjugate w r (q-a) = endpointConjugate w r q-endpointConjugate w r a := by
  apply Subtype.ext
  funext k
  simp only [endpointConjugate_apply, WeightedCoeff.sub_val, map_sub]

/-- The corrected physical strip is invariant under spectral conjugation. -/
theorem mem_reducedHillStrip_conj (n : ℕ) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    (starRingEnd ℂ) z ∈ reducedHillStrip n := by
  simpa only [reducedHillStrip, Set.mem_ofPred_eq, Complex.conj_re] using hz

/-- Conjugation reverses the original free Fourier symbol, with the same removed modes. -/
theorem reducedHillSymbol_conj (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    reducedHillSymbol n hn ((starRingEnd ℂ) z) (mem_reducedHillStrip_conj n z hz) k =
      (starRingEnd ℂ) (reducedHillSymbol n hn z hz (-k)) := by
  change (if k.natAbs = n then 0 else ((starRingEnd ℂ) z-(freeHillValue k:ℂ))⁻¹) =
    (starRingEnd ℂ) (if (-k).natAbs = n then 0 else (z-(freeHillValue (-k):ℂ))⁻¹)
  simp only [Int.natAbs_neg, freeHillValue_neg]
  split_ifs <;> simp

/-- The actual infinite Fourier perturbation commutes with physical conjugation. -/
theorem unshiftedEndpointHillPerturbation_conj (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointConjugate w r (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a) =
      unshiftedEndpointHillPerturbation w r hr hr1 n hn ((starRingEnd ℂ) z)
        (mem_reducedHillStrip_conj n z hz) (endpointConjugate w r q) (endpointConjugate w r a) := by
  apply Subtype.ext
  funext m
  simp only [endpointConjugate_apply, unshiftedEndpointHillPerturbation_apply]
  rw [Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq
    (fun k : ℤ => (starRingEnd ℂ) (q.val (-m-k)*reducedHillSymbol n hn z hz k*a.val k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, map_mul]
  rw [show -m- -k = -(m-k) by omega]
  exact congrArg (fun t : ℂ => (starRingEnd ℂ) (q.val (-(m-k)))*t*(starRingEnd ℂ) (a.val (-k)))
    (reducedHillSymbol_conj n hn z hz k).symm

/-- Uniqueness of the actual tail equation identifies the conjugated inverse. -/
theorem endpointHillTailInverse_conj (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointConjugate w r (endpointHillTailInverse w r hr hr1 n hn z hz q hs a) =
      endpointHillTailInverse w r hr hr1 n hn ((starRingEnd ℂ) z) (mem_reducedHillStrip_conj n z hz)
        (endpointConjugate w r q) (by simpa only [norm_endpointConjugate] using hs) (endpointConjugate w r a) := by
  apply endpointHillTailInverse_unique
  have he := congrArg (endpointConjugate w r)
    (endpointHillTailInverse_right w r hr hr1 n hn z hz q hs a)
  rwa [endpointConjugate_sub, unshiftedEndpointHillPerturbation_conj] at he

/-- Physical conjugation exchanges the two signed resonant forcing modes. -/
theorem negativeModulation_conj (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (j : ℤ) :
    endpointConjugate w r (w.negativeModulation r hr j q) =
      w.negativeModulation r hr (-j) (endpointConjugate w r q) := by
  apply Subtype.ext
  funext k
  simp only [endpointConjugate_apply, SpectralWeight.negativeModulation_apply]
  rw [show -k-j = -(k- -j) by omega]

/-- The proved corrected Fourier modes have the physical column-swap symmetry. -/
theorem endpointHillCorrectedMode_conj (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (j : ℤ) :
    endpointConjugate w r (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) =
      endpointHillCorrectedMode w r hr hr1 n hn ((starRingEnd ℂ) z) (mem_reducedHillStrip_conj n z hz)
        (endpointConjugate w r q) (by simpa only [norm_endpointConjugate] using hs) (-j) := by
  unfold endpointHillCorrectedMode
  rw [endpointHillTailInverse_conj, negativeModulation_conj]

/-- The actual physical diagonal and both off-diagonal entries have their
literal conjugation symmetries. Diagonal equality is supplied by Green symmetry. -/
theorem endpointCoefficients_conj (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointDiagonal r hr hr1 n (endpointConjugate SpectralWeight.one r q,(starRingEnd ℂ) z) =
        (starRingEnd ℂ) (endpointDiagonal r hr hr1 n (q,z)) ∧
      endpointUpperCoupling r hr hr1 n (endpointConjugate SpectralWeight.one r q,(starRingEnd ℂ) z) =
        (starRingEnd ℂ) (endpointLowerCoupling r hr hr1 n (q,z)) ∧
      endpointLowerCoupling r hr hr1 n (endpointConjugate SpectralWeight.one r q,(starRingEnd ℂ) z) =
        (starRingEnd ℂ) (endpointUpperCoupling r hr hr1 n (q,z)) := by
  have hp := endpointHillCorrectedMode_conj SpectralWeight.one r hr hr1 n hn z hz q hs (n:ℤ)
  have hm := endpointHillCorrectedMode_conj SpectralWeight.one r hr hr1 n hn z hz q hs (-(n:ℤ))
  simp only [endpointHillCorrectedMode_pos, endpointHillCorrectedMode_neg, neg_neg] at hp hm
  have hdiag := endpointHillEffectivePotential_diagonals_eq r hr hr1 n hn z hz q hs
  simp only [endpointDiagonal, endpointUpperCoupling, endpointLowerCoupling,
    endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs,
    endpointEffectiveFamily_eq r hr hr1 n hn (endpointConjugate SpectralWeight.one r q,(starRingEnd ℂ) z)
      (mem_reducedHillStrip_conj n z hz) (by simpa only [norm_endpointConjugate] using hs)]
  refine ⟨?_, ?_, ?_⟩
  · have he := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val (n:ℤ)) hm
    simpa only [endpointConjugate_apply, ← hdiag] using he.symm
  · have he := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val (n:ℤ)) hp
    simpa only [endpointConjugate_apply] using he.symm
  · have he := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val (-(n:ℤ))) hm
    simpa only [endpointConjugate_apply, neg_neg] using he.symm

end NLS.KdV
