import NLS

/-!
Public-API checks: the `p=1` endpoint, a Hilbert exponent, a non-Hilbert exponent,
the separate `p=∞` convolution and derivative endpoints, and frequency signs.
Operator checks cover the domain inclusion, signed free eigenmodes, a nonzero
potential coupling, and the spectral equation between distinct spaces.
-/

open scoped ENNReal
open NLS

noncomputable section

local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

example (φ : Coeff 1) (f : ZakharovShabat.ScalarDomain 1) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 1 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (φ : Coeff 2) (f : ZakharovShabat.ScalarDomain 2) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 2 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (φ : Coeff 3) (f : ZakharovShabat.ScalarDomain 3) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (a : Coeff ⊤) (b : Coeff 1) :
    ‖Coeff.convolution a b‖ ≤ ‖a‖ * ‖b‖ := Coeff.norm_convolution_le a b

example (a : Coeff 2) : Coeff.convolution a (lp.single 1 3 1) (-2) = a (-5) := by
  rw [Coeff.convolution_single_right]
  simp

example (f : ZakharovShabat.ScalarDomain 3) (n : ℤ) :
    ZakharovShabat.potentialMul (by simp) (lp.single 3 0 1) f n = f.val n :=
  ZakharovShabat.potentialMul_unit_apply (by simp) f n

open ZakharovShabat

-- The differential part also exists at infinity; density is asserted only for finite p.
example (f : ScalarDomain ⊤) : ‖derivative f‖ ≤ Real.pi * ‖f‖ :=
  norm_derivative_le f

example : DenseRange (domainInclusion (p := 1)) :=
  domainInclusion_denseRange (by simp)

example (φ : PairSpace 3) (f : Domain 3) :
    ‖operator (by simp) φ f‖ ≤
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) * ‖φ‖) * ‖f‖ :=
  norm_operator_apply_le (by simp) φ f

-- Differentiation of exp(2 i π x) has coefficient 2 i π at frequency two.
example : derivative (scalarMode (p := 2) 2 1) 2 = 2 * Complex.I * (Real.pi : ℂ) := by
  simp
  ring

-- The negative signed component uses scalar frequency -n, but eigenvalue +π n.
example (n : ℤ) :
    spectralPencil (p := 2) (by simp) 0 ((Real.pi : ℂ) * n) (negativeMode n) = 0 := by
  simp [freeOperator_negativeMode]

example (n : ℤ) :
    spectralPencil (p := 3) (by simp) 0 ((Real.pi : ℂ) * n) (positiveMode n) = 0 := by
  simp [freeOperator_positiveMode]

-- A unit off-diagonal potential feeds each opposite component into the output.
example (f : Domain 3) :
    potentialOperator (by simp) (lp.single 3 0 1, lp.single 3 0 1) f =
      (scalarInclusion f.2, scalarInclusion f.1) :=
  potentialOperator_unit (by simp) f

-- With just φ₋ = 1, a positive mode creates the expected first-component coefficient.
example :
    (operator (p := 1) (by simp) (lp.single 1 0 1, 0) (positiveMode 4)).1 4 = 1 := by
  simp [operator_fst_apply, positiveMode, lp.single_apply, Pi.single_apply]

-- Nonreal parameters supply concrete, non-vacuous instances of the resolvent API.
private theorem I_off_freeLattice : Complex.I ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by simp)

example (a : PairSpace 1) :
    freePencil Complex.I (freeResolventToDomain Complex.I I_off_freeLattice a) = a :=
  freePencil_freeResolventToDomain _ _ a

example (f : Domain 3) :
    freeResolventToDomain Complex.I I_off_freeLattice (freePencil Complex.I f) = f :=
  freeResolventToDomain_freePencil _ _ f

example : ‖freeResolventToDomain (p := 2) Complex.I I_off_freeLattice‖ ≤
    freeDomainBound Complex.I := norm_freeResolventToDomain_le _ _

example (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolvent (p := 3) z hz‖ ≤ (freeGap z)⁻¹ := norm_freeResolvent_le z hz

example : IsCompactOperator (freeResolvent (p := 1) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

example : IsCompactOperator (freeResolvent (p := 3) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

-- Compactness here also covers infinity, unlike the finite-p domain-density theorem.
example : IsCompactOperator (freeResolvent (p := ⊤) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

example : (freeResolvent (p := 2) Complex.I I_off_freeLattice
    (lp.single 2 0 1, 0)).1 0 = -Complex.I := by
  simp [lp.single_apply]

-- The signed negative mode still has denominator I - π n, not I + π n.
example (n : ℤ) :
    freeResolvent Complex.I I_off_freeLattice (domainInclusion (negativeMode (p := 3) n)) =
      (Complex.I - (Real.pi : ℂ) * n)⁻¹ • domainInclusion (negativeMode n) :=
  freeResolvent_negativeMode _ _ n

example (z : ℂ) (hz : z ∉ freeLattice) :
    Filter.Tendsto
      (fun s : Finset ℤ => (Coeff.truncateCLM s).comp (scalarResolvent (p := 2) z hz))
      Filter.atTop (nhds (scalarResolvent z hz)) :=
  tendsto_scalarResolvent_cutoff z hz

example (z w : ℂ) (hz : z ∉ freeLattice) (hw : w ∉ freeLattice) :
    freeResolvent (p := 2) z hz - freeResolvent w hw =
      (w - z) • (freeResolvent z hz).comp (freeResolvent w hw) :=
  freeResolvent_identity z w hz hw
