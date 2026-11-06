import NLS.SequenceSpaces.PositiveDeletedProjection
import NLS.SequenceSpaces.PhysicalRealDeletedHilbert
import NLS.SequenceSpaces.QuadraticActionsExponent
import NLS.SequenceSpaces.RealFormIdentity

/-! # Actual signed Fourier coordinates and Cartesian action pairs

Positive projection retains the original integer labels. The bounded map
from Cartesian pairs is onto the entire zero-mode-deleted complex space;
its canonical section is supported on positive indices. Physical conjugate
reflection corresponds to pointwise-real Cartesian pairs, and the signed
product is exactly half the Cartesian squared radius.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff

/-- The exact 1/sqrt(2) Cartesian normalization. -/
def signedCartesianScale : ℂ := (Real.sqrt 2 : ℂ)/2

theorem signedCartesianScale_sq : signedCartesianScale^2 = 1/2 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [signedCartesianScale,div_pow,hs]
  norm_num

theorem conj_signedCartesianScale : conj signedCartesianScale = signedCartesianScale := by
  simp only [signedCartesianScale,map_div₀,conj_ofReal,map_ofNat]

def cartesianSignedRaw : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2 :=
  signedCartesianScale • ((positiveDeletedProjection 2 0).comp
      (ContinuousLinearMap.fst ℂ _ _-I • ContinuousLinearMap.snd ℂ _ _)+
    reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((positiveDeletedProjection 2 0).comp
        (ContinuousLinearMap.fst ℂ _ _+I • ContinuousLinearMap.snd ℂ _ _)))

theorem cartesianSignedRaw_pos (z : Coeff 2 × Coeff 2) (n : ℤ) (hn : 0 < n) :
    cartesianSignedRaw z n = signedCartesianScale*(z.1 n-I*z.2 n) := by
  change signedCartesianScale*((positiveDeletedProjection 2 0 (z.1-I • z.2)) n+
    (positiveDeletedProjection 2 0 (z.1+I • z.2)) (-n)) = _
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply,
    if_pos (by omega),if_neg (by omega),add_zero]
  rfl

theorem cartesianSignedRaw_neg (z : Coeff 2 × Coeff 2) (n : ℤ) (hn : 0 < n) :
    cartesianSignedRaw z (-n) = signedCartesianScale*(z.1 n+I*z.2 n) := by
  change signedCartesianScale*((positiveDeletedProjection 2 0 (z.1-I • z.2)) (-n)+
    (positiveDeletedProjection 2 0 (z.1+I • z.2)) (-(-n))) = _
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply,
    if_neg (by omega),if_pos (by omega),zero_add,neg_neg]
  rfl

theorem cartesianSignedRaw_zero (z : Coeff 2 × Coeff 2) : cartesianSignedRaw z 0 = 0 := by
  change signedCartesianScale*((positiveDeletedProjection 2 0 (z.1-I • z.2)) 0+
    (positiveDeletedProjection 2 0 (z.1+I • z.2)) (-0)) = _
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply]
  norm_num

/-- The actual full signed sequence, with central coefficient zero. -/
def cartesianToSigned : (Coeff 2 × Coeff 2) →L[ℂ] DeletedCoeff 2 0 :=
  cartesianSignedRaw.codRestrict _ cartesianSignedRaw_zero

@[simp] theorem cartesianToSigned_val (z : Coeff 2 × Coeff 2) :
    (cartesianToSigned z).val = cartesianSignedRaw z := rfl

/-- The canonical positive Cartesian section of every original signed sequence. -/
def signedToCartesian : DeletedCoeff 2 0 →L[ℂ] (Coeff 2 × Coeff 2) :=
  let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL
  let R := reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp L
  (signedCartesianScale • ((positiveDeletedProjection 2 0).comp (L+R))).prod
    ((signedCartesianScale*I) • ((positiveDeletedProjection 2 0).comp (L-R)))

theorem signedToCartesian_pos (a : DeletedCoeff 2 0) (n : ℤ) (hn : 0 < n) :
    (signedToCartesian a).1 n = signedCartesianScale*(a.val n+a.val (-n)) ∧
      (signedToCartesian a).2 n = signedCartesianScale*I*(a.val n-a.val (-n)) := by
  change signedCartesianScale*((positiveDeletedProjection 2 0 (a.val+reflection a.val)) n) = _ ∧
    (signedCartesianScale*I)*((positiveDeletedProjection 2 0 (a.val-reflection a.val)) n) = _
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply]
  simp only [if_pos (by omega : 0<n ∧ n≠0)]
  exact ⟨rfl,rfl⟩

theorem signedToCartesian_nonpos (a : DeletedCoeff 2 0) (n : ℤ) (hn : n ≤ 0) :
    (signedToCartesian a).1 n = 0 ∧ (signedToCartesian a).2 n = 0 := by
  change signedCartesianScale*((positiveDeletedProjection 2 0 (a.val+reflection a.val)) n) = 0 ∧
    (signedCartesianScale*I)*((positiveDeletedProjection 2 0 (a.val-reflection a.val)) n) = 0
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply]
  simp only [if_neg (by omega : ¬(0<n ∧ n≠0))]
  exact ⟨mul_zero _,mul_zero _⟩

/-- No actual signed frequency, phase or amplitude is lost in the section. -/
theorem cartesianToSigned_signedToCartesian (a : DeletedCoeff 2 0) :
    cartesianToSigned (signedToCartesian a) = a := by
  apply Subtype.ext
  ext n
  change cartesianSignedRaw (signedToCartesian a) n = a.val n
  by_cases hp : 0 < n
  · rw [cartesianSignedRaw_pos _ n hp,(signedToCartesian_pos a n hp).1,
      (signedToCartesian_pos a n hp).2]
    calc
      _ = 2*signedCartesianScale^2*a.val n := by ring_nf; simp only [I_sq]; ring
      _ = _ := by rw [signedCartesianScale_sq]; ring
  · by_cases hn : n < 0
    · have hm : 0 < -n := by omega
      have he : n = -(-n) := by omega
      rw [he,cartesianSignedRaw_neg _ (-n) hm,(signedToCartesian_pos a (-n) hm).1,
        (signedToCartesian_pos a (-n) hm).2,neg_neg]
      calc
        _ = 2*signedCartesianScale^2*a.val n := by ring_nf; simp only [I_sq]; ring
        _ = _ := by rw [signedCartesianScale_sq]; ring
    · have hn0 : n = 0 := by omega
      subst n
      exact (cartesianSignedRaw_zero _).trans a.property.symm

/-- The original signed product is EXACTLY the usual quadratic action. -/
theorem cartesianToSigned_product (z : Coeff 2 × Coeff 2) (n : ℤ) (hn : 0 < n) :
    (cartesianToSigned z).val n*(cartesianToSigned z).val (-n) =
      quadraticActionsExponent (q := 1) z n := by
  rw [cartesianToSigned_val,cartesianSignedRaw_pos _ n hn,cartesianSignedRaw_neg _ n hn,
    quadraticActionsExponent_apply]
  calc
    _ = signedCartesianScale^2*(z.1 n^2+z.2 n^2) := by ring_nf; simp only [I_sq]; ring
    _ = _ := by rw [signedCartesianScale_sq]; ring

/-- Canonical actions retain the original positive indices and vanish elsewhere. -/
theorem quadraticActions_signedToCartesian (a : DeletedCoeff 2 0) (n : ℤ) :
    quadraticActionsExponent (q := 1) (signedToCartesian a) n =
      if 0 < n then a.val n*a.val (-n) else 0 := by
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have he := cartesianToSigned_product (signedToCartesian a) n hn
    rw [cartesianToSigned_signedToCartesian] at he
    exact he.symm
  · rw [if_neg hn,quadraticActionsExponent_apply,
      (signedToCartesian_nonpos a n (by omega)).1,(signedToCartesian_nonpos a n (by omega)).2]
    norm_num

/-- Real Cartesian pairs give precisely the physical conjugate-reflected signed form. -/
theorem cartesianToSigned_real (z : Coeff 2 × Coeff 2) (hz : z ∈ realPairLocus 2) :
    cartesianToSigned z ∈ physicalRealDeletedSubmodule := by
  apply Subtype.ext
  ext n
  change conj ((cartesianToSigned z).val (-n)) = (cartesianToSigned z).val n
  have hx (k : ℤ) : conj (z.1 k) = z.1 k := by
    apply Complex.ext <;> simp only [conj_re,conj_im,hz.1 k,neg_zero]
  have hy (k : ℤ) : conj (z.2 k) = z.2 k := by
    apply Complex.ext <;> simp only [conj_re,conj_im,hz.2 k,neg_zero]
  by_cases hp : 0 < n
  · simp only [cartesianToSigned_val,cartesianSignedRaw_pos _ n hp,cartesianSignedRaw_neg _ n hp,
      map_mul,map_add,conj_signedCartesianScale,conj_I,hx,hy]
    ring
  · by_cases hn : n < 0
    · have hm : 0 < -n := by omega
      have he : n = -(-n) := by omega
      rw [he]
      simp only [cartesianToSigned_val,neg_neg,cartesianSignedRaw_pos _ (-n) hm,
        cartesianSignedRaw_neg _ (-n) hm,map_mul,map_sub,conj_signedCartesianScale,conj_I,hx,hy]
      ring
    · have hn0 : n = 0 := by omega
      subst n
      simp only [cartesianToSigned_val,neg_zero,cartesianSignedRaw_zero,map_zero]

/-- Every actual physical real signed sequence has a real Cartesian section. -/
theorem signedToCartesian_real (a : physicalRealDeletedSubmodule) :
    signedToCartesian a.val ∈ realPairLocus 2 := by
  have ha (n : ℤ) : conj (a.val.val (-n)) = a.val.val n := by
    have he := congrArg (fun b : DeletedCoeff 2 0 => b.val n) a.property
    exact he
  have ha' (n : ℤ) : conj (a.val.val n) = a.val.val (-n) := by
    simpa only [neg_neg] using ha (-n)
  have hX (n : ℤ) : conj ((signedToCartesian a.val).1 n) = (signedToCartesian a.val).1 n := by
    by_cases hn : 0 < n
    · rw [(signedToCartesian_pos a.val n hn).1]
      simp only [map_mul,map_add,conj_signedCartesianScale,ha,ha']
      ring
    · rw [(signedToCartesian_nonpos a.val n (by omega)).1,map_zero]
  have hY (n : ℤ) : conj ((signedToCartesian a.val).2 n) = (signedToCartesian a.val).2 n := by
    by_cases hn : 0 < n
    · rw [(signedToCartesian_pos a.val n hn).2]
      simp only [map_mul,map_sub,conj_signedCartesianScale,conj_I,ha,ha']
      ring
    · rw [(signedToCartesian_nonpos a.val n (by omega)).2,map_zero]
  constructor <;> intro n
  · have he := congrArg Complex.im (hX n)
    simp only [conj_im] at he
    linarith
  · have he := congrArg Complex.im (hY n)
    simp only [conj_im] at he
    linarith

end NLS.Coeff
