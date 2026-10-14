import NLS.ZakharovShabat.ConstantResonantCoefficient
import NLS.ZakharovShabat.SingleResonantPotential

/-!
# An exactly cubic off-diagonal resonant coefficient

A potential supported at first-component frequency 2n and second-component
frequency zero has an explicit three-mode corrected vector. Its positive
coefficient is ab²/(2πn)² at a nonzero center. This isolates the amplitude
scaling needed to audit the missing powers in Lemma 6.8(ii).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- Two physical modes producing an exactly cubic positive correction. -/
def cubicPotential (w : SpectralWeight) (n : ℤ) (a b : ℂ) : WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.toMax w.toWeight p).symm (weightedMode w.toWeight (2*n) a,weightedMode w.toWeight 0 b)

@[simp] theorem cubicPotential_fst (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (cubicPotential (p := p) w n a b).fst.val k = if k=2*n then a else 0 := weightedMode_apply _ _ _ _
@[simp] theorem cubicPotential_snd (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (cubicPotential (p := p) w n a b).snd.val k = if k=0 then b else 0 := weightedMode_apply _ _ _ _
@[simp] theorem cubicPotential_domain_fst (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (cubicPotential w n a b) f).fst.val k = a*f.snd.val (k-2*n) := by
  rw [weightedDomainPotential_fst]
  have he (j : ℤ) : k-j=2*n ↔ j=k-2*n := by omega
  simp [ite_mul,he]
@[simp] theorem cubicPotential_domain_snd (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (cubicPotential w n a b) f).snd.val k = b*f.fst.val k := by
  rw [weightedDomainPotential_snd]
  simp [ite_mul,sub_eq_zero]
@[simp] theorem cubicPotential_inverse_fst (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (cubicPotential w n a b) n z hz f).fst.val k =
      a*(complementarySymbol n z (k-2*n)*f.snd.val (k-2*n)) := by
  have he := congrArg (fun v => v.fst.val k)
    (weightedDomainPotential_complementaryInverse hp w (cubicPotential w n a b) f n z hz)
  simpa only [cubicPotential_domain_fst,complementaryFreeDomainInverse_snd] using he.symm
@[simp] theorem cubicPotential_inverse_snd (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (cubicPotential w n a b) n z hz f).snd.val k =
      b*(complementarySymbol n z (-k)*f.fst.val k) := by
  have he := congrArg (fun v => v.snd.val k)
    (weightedDomainPotential_complementaryInverse hp w (cubicPotential w n a b) f n z hz)
  simpa only [cubicPotential_domain_snd,complementaryFreeDomainInverse_fst] using he.symm
/-- Exact coefficient from a finite solution of the correction equation. -/
theorem cubicPotential_bplus (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : n ≠ 0)
    (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w (cubicPotential w n a b) n z hz‖ < 1) :
    weightedResonantBPlus hp w (cubicPotential w n a b) n z hz h = a*b^2*(complementarySymbol n z (-n))^2 := by
  let φ := cubicPotential (p := p) w n a b
  let u := resonantSynthesis (p := p) w.toWeight.oneDerivative n (Pi.single 0 1)
  let s := complementarySymbol n z (-n)
  let x := weightedPairMode (p := p) w.toWeight (-n) 0 b + weightedPairMode w.toWeight n (a*b*s) (a*b^2*s^2)
  have hx : x - weightedPotentialInverse hp w φ n z hz x = weightedDomainPotential hp w φ u := by
    apply weightedPair_ext <;> intro k
    · change x.fst.val k - (weightedPotentialInverse hp w (cubicPotential w n a b) n z hz x).fst.val k =
        (weightedDomainPotential hp w (cubicPotential w n a b) u).fst.val k
      rw [cubicPotential_inverse_fst,cubicPotential_domain_fst]
      have he : k-2*n = -n ↔ k=n := by omega
      have he' : k-2*n = n ↔ k=3*n := by omega
      by_cases hk : k=n
      · subst k
        simp [x,u,show n ≠ -n by omega,show -n ≠ n by omega,show n-2*n = -n by omega,s]
        ring
      · by_cases hk' : k=3*n
        · subst k
          simp [x,u,hk,show 3*n ≠ -n by omega,show 3*n-2*n=n by omega]
        · simp [x,u,he,he',hk,hk']
    · change x.snd.val k - (weightedPotentialInverse hp w (cubicPotential w n a b) n z hz x).snd.val k =
        (weightedDomainPotential hp w (cubicPotential w n a b) u).snd.val k
      rw [cubicPotential_inverse_snd,cubicPotential_domain_snd]
      by_cases hk : k=n
      · subst k
        simp [x,u,show n ≠ -n by omega,s]
        ring
      · simp [x,u,hk]
  have he := weightedCorrection_unique hp w φ n z hz h x (weightedDomainPotential hp w φ u) hx
  unfold weightedResonantBPlus weightedCorrectionMatrix
  rw [resonantCoordinates_one]
  have hv := congrArg (fun v => v.snd.val n) he
  simpa [x,s,show n ≠ -n by omega] using hv.symm
/-- The center value is cubic in the amplitudes. -/
theorem cubicPotential_bplus_center (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : n ≠ 0)
    (a b : ℂ)
    (h : ‖weightedPotentialSquareInShift hp w (cubicPotential w n a b) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    weightedResonantBPlus hp w (cubicPotential w n a b) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) h = a*b^2/((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2 := by
  rw [cubicPotential_bplus hp w n hn a b _ _ h,complementarySymbol,if_neg (by omega : -n ≠ n)]
  have hd : (Real.pi : ℂ)*n-(Real.pi : ℂ)*(-n : ℤ) = ((2*Real.pi*(n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hd]
  ring

/-- Exact unit-weight Hilbert norm of the two-mode potential. -/
theorem cubicPotential_norm_sq (n : ℤ) (a b : ℂ) :
    ‖cubicPotential (p := 2) SpectralWeight.one n a b‖^2 = ‖a‖^2+‖b‖^2 := by
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num)
    (cubicPotential (p := 2) SpectralWeight.one n a b)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  change ‖cubicPotential (p := 2) SpectralWeight.one n a b‖^2 =
    ‖weightedMode (p := 2) SpectralWeight.one.toWeight (2*n) a‖^2 +
    ‖weightedMode (p := 2) SpectralWeight.one.toWeight 0 b‖^2 at h
  simpa only [norm_weightedMode_one] using h
end NLS.ZakharovShabat
