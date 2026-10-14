import NLS.ZakharovShabat.ConstantResonantCoefficient
import NLS.ZakharovShabat.SingleResonantPotential
import NLS.SequenceSpaces.WeightedFourierTail

/-!
# A reversed two-mode potential for the component-norm audit

The first component is constant and the second has frequency -2n.
The negative resonant coefficient is a²b/(2πn)² at the free center.
Near the constant potential (1,0), its squared size is quadratic in b,
whereas the printed positive-component budget is quartic.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- Constant first component and a single second-component frequency -2n. -/
def reverseCubicPotential (w : SpectralWeight) (n : ℤ) (a b : ℂ) : WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.toMax w.toWeight p).symm (weightedMode w.toWeight 0 a,weightedMode w.toWeight (-(2*n)) b)
@[simp] theorem reverseCubicPotential_fst (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (reverseCubicPotential (p := p) w n a b).fst.val k = if k=0 then a else 0 := weightedMode_apply _ _ _ _
@[simp] theorem reverseCubicPotential_snd (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (reverseCubicPotential (p := p) w n a b).snd.val k = if k= -(2*n) then b else 0 := weightedMode_apply _ _ _ _
@[simp] theorem reverseCubicPotential_domain_fst (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (reverseCubicPotential w n a b) f).fst.val k = a*f.snd.val k := by
  rw [weightedDomainPotential_fst]
  simp [ite_mul,sub_eq_zero]
@[simp] theorem reverseCubicPotential_domain_snd (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (reverseCubicPotential w n a b) f).snd.val k = b*f.fst.val (k+2*n) := by
  rw [weightedDomainPotential_snd]
  have he (j : ℤ) : k-j= -(2*n) ↔ j=k+2*n := by omega
  simp [ite_mul,he]
@[simp] theorem reverseCubicPotential_inverse_fst (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (reverseCubicPotential w n a b) n z hz f).fst.val k =
      a*(complementarySymbol n z k*f.snd.val k) := by
  have he := congrArg (fun v => v.fst.val k)
    (weightedDomainPotential_complementaryInverse hp w (reverseCubicPotential w n a b) f n z hz)
  simpa only [reverseCubicPotential_domain_fst,complementaryFreeDomainInverse_snd] using he.symm
@[simp] theorem reverseCubicPotential_inverse_snd (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (reverseCubicPotential w n a b) n z hz f).snd.val k =
      b*(complementarySymbol n z (-(k+2*n))*f.fst.val (k+2*n)) := by
  have he := congrArg (fun v => v.snd.val k)
    (weightedDomainPotential_complementaryInverse hp w (reverseCubicPotential w n a b) f n z hz)
  simpa only [reverseCubicPotential_domain_snd,complementaryFreeDomainInverse_fst] using he.symm

/-- Exact negative coefficient from a three-mode correction vector. -/
theorem reverseCubicPotential_bminus (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : n ≠ 0)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w (reverseCubicPotential w n a b) n z hz‖ < 1) :
    weightedResonantBMinus hp w (reverseCubicPotential w n a b) n z hz h = a^2*b*(complementarySymbol n z (-n))^2 := by
  let φ := reverseCubicPotential (p := p) w n a b
  let u := resonantSynthesis (p := p) w.toWeight.oneDerivative n (Pi.single 1 1)
  let s := complementarySymbol n z (-n)
  let x := weightedPairMode (p := p) w.toWeight n a 0 + weightedPairMode w.toWeight (-n) (a^2*b*s^2) (a*b*s)
  have hx : x - weightedPotentialInverse hp w φ n z hz x = weightedDomainPotential hp w φ u := by
    apply weightedPair_ext <;> intro k
    · change x.fst.val k - (weightedPotentialInverse hp w (reverseCubicPotential w n a b) n z hz x).fst.val k =
        (weightedDomainPotential hp w (reverseCubicPotential w n a b) u).fst.val k
      rw [reverseCubicPotential_inverse_fst,reverseCubicPotential_domain_fst]
      by_cases hk : k= -n
      · subst k
        simp [x,u,show -n ≠ n by omega,s]
        ring
      · simp [x,u,hk]
    · change x.snd.val k - (weightedPotentialInverse hp w (reverseCubicPotential w n a b) n z hz x).snd.val k =
        (weightedDomainPotential hp w (reverseCubicPotential w n a b) u).snd.val k
      rw [reverseCubicPotential_inverse_snd,reverseCubicPotential_domain_snd]
      have he : k+2*n=n ↔ k= -n := by omega
      have he' : k+2*n= -n ↔ k= -(3*n) := by omega
      by_cases hk : k= -n
      · subst k
        simp [x,u,show n ≠ -n by omega,show -n ≠ n by omega,show -n+2*n=n by omega,s]
        ring
      · by_cases hk' : k= -(3*n)
        · subst k
          simp [x,u,hk,show -(3*n) ≠ n by omega,show -(3*n)+2*n= -n by omega]
        · simp [x,u,he,he',hk,hk']
  have he := weightedCorrection_unique hp w φ n z hz h x (weightedDomainPotential hp w φ u) hx
  unfold weightedResonantBMinus weightedCorrectionMatrix
  rw [resonantCoordinates_zero]
  have hv := congrArg (fun v => v.fst.val (-n)) he
  simpa [x,s,show -n ≠ n by omega] using hv.symm
/-- Exact center value of the negative coefficient. -/
theorem reverseCubicPotential_bminus_center (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : n ≠ 0)
    (a b : ℂ)
    (h : ‖weightedPotentialSquareInShift hp w (reverseCubicPotential w n a b) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    weightedResonantBMinus hp w (reverseCubicPotential w n a b) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) h = a^2*b/((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
  rw [reverseCubicPotential_bminus hp w n hn a b _ _ h,complementarySymbol,if_neg (by omega : -n ≠ n)]
  have hd : (Real.pi : ℂ)*n-(Real.pi : ℂ)*(-n : ℤ) = ((2*Real.pi*(n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hd]
  ring

/-- Exact Hilbert distance from the fixed constant background. -/
theorem reverseCubicPotential_distance_sq (n : ℤ) (b : ℂ) :
    ‖reverseCubicPotential (p := 2) SpectralWeight.one n 1 b - constantSpectralPotential SpectralWeight.one 1 0‖^2 = ‖b‖^2 := by
  let φ := reverseCubicPotential (p := 2) SpectralWeight.one n 1 b - constantSpectralPotential SpectralWeight.one 1 0
  have hf : φ.fst = 0 := by apply Subtype.ext; funext k; simp [φ,constantSpectralPotential]
  have hs : φ.snd = weightedMode SpectralWeight.one.toWeight (-(2*n)) b := by apply Subtype.ext; funext k; simp [φ,constantSpectralPotential]
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num) φ
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  change ‖φ‖^2 = ‖b‖^2
  rw [h,hf,hs]
  simp [norm_weightedMode_one]
/-- A positive cutoff removes the constant first component. -/
theorem reverseCubicPotential_tail_norm_sq_le (n : ℤ) (b : ℂ) (K : ℕ) (hK : 1 ≤ K) :
    ‖weightedPairFourierTail SpectralWeight.one.toWeight K (reverseCubicPotential (p := 2) SpectralWeight.one n 1 b)‖^2 ≤ ‖b‖^2 := by
  let φ := weightedPairFourierTail SpectralWeight.one.toWeight K (reverseCubicPotential (p := 2) SpectralWeight.one n 1 b)
  have hf : φ.fst = 0 := by
    apply Subtype.ext
    funext k
    by_cases hk : k=0 <;> simp [φ,hk,show ¬K ≤ 0 by omega]
  have hs : ‖φ.snd‖ ≤ ‖b‖ := by
    change ‖WeightedCoeff.fourierTail SpectralWeight.one.toWeight K (weightedMode SpectralWeight.one.toWeight (-(2*n)) b)‖ ≤ ‖b‖
    exact (WeightedCoeff.norm_fourierTail_le _ _ _).trans_eq (norm_weightedMode_one _ _)
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num) φ
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  change ‖φ‖^2 ≤ ‖b‖^2
  rw [h,hf]
  simp only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add]
  gcongr
end NLS.ZakharovShabat
