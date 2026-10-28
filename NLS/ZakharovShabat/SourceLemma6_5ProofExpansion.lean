import NLS.ZakharovShabat.SourceLemma6_5ProofSeries

/-! # The full double Fourier expansion in Lemma 6.5

The signed product-index series converges in the original weighted l1 pair
norm. Its representative has exactly the coefficients of the actual original
derivative-domain vector. Both exclusions and literal denominators remain
valid throughout every closed strip, including free centers.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Raw Fourier modes have their exact weighted norm. -/
theorem sourceLemma65Vector_mode_norm (w : Weight) (k : ℤ) (c : ℂ) :
    ‖weightedMode (p := p) w k c‖ = w k * ‖c‖ := by
  simp [weightedMode, norm_smul, lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)),
    Complex.norm_real, abs_of_pos (w.positive k), mul_comm]

/-- Full product-index Fourier modes converge absolutely in the original weighted l1 space. -/
theorem sourceLemma65Vector_summable (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    Summable (fun kl : ℤ × ℤ => ‖weightedMode (p := 1) w.toWeight kl.1
      (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 *
        φ.val (kl.1+kl.2) * f.val (-kl.2))‖) := by
  apply ((sourceLemma65ProofTerm_summable hp w φ f n).mul_left (w n)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro kl
  rw [sourceLemma65Vector_mode_norm]
  have hw : w kl.1 ≤ w (kl.1-n)*w n := by
    simpa only [sub_add_cancel] using w.add_le (kl.1-n) n
  have h1 := mul_le_mul_of_nonneg_right hw (norm_nonneg
    (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 * φ.val (kl.1+kl.2) * f.val (-kl.2)))
  have h2 := mul_le_mul_of_nonneg_left (sourceLemma65ProofTerm_pointwise w φ f hz kl.1 kl.2) (w.positive n).le
  nlinarith only [h1,h2]

/-- The literal double Fourier series represents the actual weighted l1 sandwich. -/
theorem sourceLemma65Vector_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    HasSum (fun kl : ℤ × ℤ => weightedMode (p := 1) w.toWeight kl.1
      (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 *
        φ.val (kl.1+kl.2) * f.val (-kl.2)))
      (complementarySandwich hp w φ n z hz false f) := by
  let V := fun kl : ℤ × ℤ => weightedMode (p := 1) w.toWeight kl.1
    (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 * φ.val (kl.1+kl.2) * f.val (-kl.2))
  have hs : Summable V := (sourceLemma65Vector_summable hp w φ f n z hz).of_norm
  suffices he : (∑' kl, V kl) = complementarySandwich hp w φ n z hz false f by
    exact he ▸ hs.hasSum
  apply Subtype.ext
  funext k
  have he := (weightedCoefficient (p := 1) w.toWeight k).map_tsum hs
  rw [weightedCoefficient_apply] at he
  have hsc := ((weightedCoefficient (p := 1) w.toWeight k).hasSum hs.hasSum).summable
  rw [he,hsc.tsum_prod]
  simp only [V,weightedCoefficient_apply,weightedMode_apply]
  rw [tsum_eq_single k]
  · simp only [ite_true]
    rw [complementarySandwich_apply]
    simp only [Bool.not_false,freeFrequency_false,freeFrequency_true]
    rw [← (Equiv.neg ℤ).tsum_eq]
    simp only [Equiv.neg_apply,neg_neg]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro l
    ring_nf
  · intro j hj
    simp [Ne.symm hj]

/-- Reflection sends a raw Fourier mode to its opposite signed mode. -/
theorem sourceLemma65Vector_reflection_mode (w : SpectralWeight) (k : ℤ) (c : ℂ) :
    w.reflection (weightedMode (p := p) w.toWeight k c) = weightedMode w.toWeight (-k) c := by
  apply Subtype.ext
  funext j
  simp only [SpectralWeight.reflection_apply,weightedMode_apply]
  by_cases hj : j = -k
  · subst j; simp
  · have hneg : -j ≠ k := by omega
    simp [hj,hneg]

/-- The first physical component has the full reflected vector-valued Fourier series. -/
theorem sourceLemma65Vector_hasSum_true (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    HasSum (fun kl : ℤ × ℤ => weightedMode (p := 1) w.toWeight (-kl.1)
      (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 *
        φ.val (-(kl.1+kl.2)) * f.val kl.2))
      (complementarySandwich hp w φ n z hz true f) := by
  rw [sourceLemma65Proof_true_reflection]
  have h := (w.reflection (p := 1)).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (sourceLemma65Vector_hasSum hp w (w.reflection φ) (w.reflection f) n z hz)
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,sourceLemma65Vector_reflection_mode,
    SpectralWeight.reflection_apply,neg_neg] using h

/-- The actual double-inverse vector viewed in the original weighted l1 pair norm. -/
def sourceLemma65Vector_original (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w.toWeight 1 :=
  let t := weightedPotentialInverse hp w φ n z hz f
  (WeightedCoeffPair.toMax w.toWeight 1).symm
    (complementaryScalarL1 hp w.toWeight n z hz true t.fst,
     complementaryScalarL1 hp w.toWeight n z hz false t.snd)

/-- Both raw components agree with the actual original derivative-domain vector. -/
theorem sourceLemma65Vector_original_coefficients (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    let t := weightedPotentialInverse hp w φ n z hz f
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz t)
    (sourceLemma65Vector_original hp w φ f n z hz).fst.val k = g.fst.val k ∧
    (sourceLemma65Vector_original hp w φ f n z hz).snd.val k = g.snd.val k := by
  simp [sourceLemma65Vector_original,WeightedCoeffPair.toMax]

/-- The full signed double Fourier series converges in the original weighted l1 pair norm. -/
theorem sourceLemma65Vector_original_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    HasSum (fun kl : ℤ × ℤ => (WeightedCoeffPair.toMax w.toWeight 1).symm
      (weightedMode (p := 1) w.toWeight (-kl.1)
        (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 *
          φ.fst.val (-(kl.1+kl.2)) * f.snd.val kl.2),
       weightedMode (p := 1) w.toWeight kl.1
        (complementarySymbol n z kl.1 * complementarySymbol n z kl.2 *
          φ.snd.val (kl.1+kl.2) * f.fst.val (-kl.2))))
      (sourceLemma65Vector_original hp w φ f n z hz) := by
  have hm := sourceLemma65Vector_hasSum_true hp w φ.fst f.snd n z hz
  have hp' := sourceLemma65Vector_hasSum hp w φ.snd f.fst n z hz
  have h := (WeightedCoeffPair.toMax w.toWeight 1).symm.toContinuousLinearMap.hasSum (hm.prodMk hp')
  have he : (WeightedCoeffPair.toMax w.toWeight 1).symm
      (complementarySandwich hp w φ.fst n z hz true f.snd,
       complementarySandwich hp w φ.snd n z hz false f.fst) = sourceLemma65Vector_original hp w φ f n z hz := by
    apply weightedPair_ext <;> intro k <;>
      simp [sourceLemma65Vector_original,WeightedCoeffPair.toMax,complementaryScalarL1_apply,
        complementarySandwich_apply,SpectralWeight.convolution_apply]
  simpa only [ContinuousLinearEquiv.coe_coe,he] using h

/-- The original double Fourier sum with both literal denominators and exclusions. -/
theorem sourceLemma65Vector_original_restricted_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    HasSum (fun kl : ℤ × ℤ => if kl.1 = n ∨ kl.2 = n then 0 else
      (WeightedCoeffPair.toMax w.toWeight 1).symm
        (weightedMode (p := 1) w.toWeight (-kl.1)
          (φ.fst.val (-(kl.1+kl.2))*f.snd.val kl.2 /
            ((z-(Real.pi:ℂ)*kl.1)*(z-(Real.pi:ℂ)*kl.2))),
         weightedMode (p := 1) w.toWeight kl.1
          (φ.snd.val (kl.1+kl.2)*f.fst.val (-kl.2) /
            ((z-(Real.pi:ℂ)*kl.1)*(z-(Real.pi:ℂ)*kl.2)))))
      (sourceLemma65Vector_original hp w φ f n z hz) := by
  convert sourceLemma65Vector_original_hasSum hp w φ f n z hz using 1
  funext kl
  by_cases hk : kl.1 = n <;> by_cases hl : kl.2 = n <;>
    simp [complementarySymbol,hk,hl,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  all_goals exact (map_zero (WeightedCoeffPair.toMax w.toWeight 1).symm).symm

/-- The weighted l1 representative has exactly the two signed scalar double inverses. -/
theorem sourceLemma65Vector_original_components (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    (sourceLemma65Vector_original hp w φ f n z hz).fst = complementarySandwich hp w φ.fst n z hz true f.snd ∧
    (sourceLemma65Vector_original hp w φ f n z hz).snd = complementarySandwich hp w φ.snd n z hz false f.fst := by
  constructor <;> apply Subtype.ext <;> funext k <;>
    simp [sourceLemma65Vector_original,WeightedCoeffPair.toMax,complementaryScalarL1_apply,
      complementarySandwich_apply,SpectralWeight.convolution_apply]

end NLS.ZakharovShabat
