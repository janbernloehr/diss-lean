import NLS.Articles.KdVConvexity.FreeLogNormingLinearization
import NLS.SequenceSpaces.PeriodOneHminusOneMeanZero
import NLS.SequenceSpaces.Insertion

/-! # The combined free spectral derivative is a Banach-space isomorphism

Disjoint positive and negative Fourier insertions reconstruct every
mean-zero H^-1 direction from the actual energy and logarithmic norming
derivatives. All formulas retain the original 1+n, 2*pi*n and signs.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def negativeDirichletIndex : ℤ ↪ ℤ where
  toFun k := -(positiveDirichletIndex k)
  inj' := by intro i j h; exact positiveDirichletIndex.injective (neg_injective h)

theorem positiveDirichletIndex_pos (k : ℤ) : 0 < positiveDirichletIndex k := by
  change (0 : ℤ) < (actionIndexEquiv k : ℤ)
  exact_mod_cast (actionIndexEquiv k).property

theorem negativeDirichletIndex_neg (k : ℤ) : negativeDirichletIndex k < 0 :=
  neg_neg_of_pos (positiveDirichletIndex_pos k)

theorem positiveDirichletIndex_not_mem_negative (k : ℤ) : positiveDirichletIndex k ∉ range negativeDirichletIndex := by
  rintro ⟨j,hj⟩
  have hpos := positiveDirichletIndex_pos k
  have hneg := negativeDirichletIndex_neg j
  omega

theorem negativeDirichletIndex_not_mem_positive (k : ℤ) : negativeDirichletIndex k ∉ range positiveDirichletIndex := by
  rintro ⟨j,hj⟩
  have hpos := positiveDirichletIndex_pos j
  have hneg := negativeDirichletIndex_neg k
  omega

def dirichletFrequencyRatioSymbol : Coeff ⊤ :=
  ⟨fun k => (actionIndexEquiv k : ℕ)/(1+(actionIndexEquiv k : ℕ) : ℂ),memℓp_infty ⟨1,by
    rintro _ ⟨k,rfl⟩
    have he : ‖(1+(actionIndexEquiv k : ℕ) : ℂ)‖ = (1+(actionIndexEquiv k : ℕ) : ℝ) := by
      have hc : (1+(actionIndexEquiv k : ℕ) : ℂ) = ((1+(actionIndexEquiv k : ℕ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hc,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    dsimp only
    rw [norm_div,Complex.norm_natCast,he]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+(actionIndexEquiv k : ℕ))).mpr
    linarith⟩⟩

def freeDirichletReconstructionCoefficients : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2 :=
  let A := ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)
  let B := (Coeff.multiplierCLM dirichletFrequencyRatioSymbol).comp (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  let P := (Coeff.insertIsometry (p := 2) positiveDirichletIndex).toContinuousLinearMap
  let N := (Coeff.insertIsometry (p := 2) negativeDirichletIndex).toContinuousLinearMap
  P.comp (-A-(2*I*(Real.pi : ℂ)) • B)+N.comp (-A+(2*I*(Real.pi : ℂ)) • B)

def freeDirichletReconstructionRaw : (Coeff 2 × Coeff 2) →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    freeDirichletReconstructionCoefficients

theorem freeDirichletReconstructionRaw_zero (z : Coeff 2 × Coeff 2) :
    (freeDirichletReconstructionRaw z).val 0 = 0 := by
  have hp : (0 : ℤ) ∉ range positiveDirichletIndex := by
    rintro ⟨k,hk⟩
    have h := positiveDirichletIndex_pos k
    omega
  have hn : (0 : ℤ) ∉ range negativeDirichletIndex := by
    rintro ⟨k,hk⟩
    have h := negativeDirichletIndex_neg k
    omega
  change (Coeff.insert positiveDirichletIndex _ 0+Coeff.insert negativeDirichletIndex _ 0)/_ = 0
  rw [Coeff.insert_apply_outside _ _ _ hp,Coeff.insert_apply_outside _ _ _ hn,zero_add,zero_div]

def freeDirichletReconstruction : (Coeff 2 × Coeff 2) →L[ℂ] PeriodOneMeanZeroHminusOne :=
  freeDirichletReconstructionRaw.codRestrict _ freeDirichletReconstructionRaw_zero

theorem freeDirichletReconstruction_positive (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (freeDirichletReconstruction z).val.val (actionIndexEquiv k : ℤ) =
      -(1+(actionIndexEquiv k : ℕ) : ℂ)*z.1 k-2*I*(Real.pi : ℂ)*(actionIndexEquiv k : ℕ)*z.2 k := by
  have hw : (Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ) =
      (1+(actionIndexEquiv k : ℕ) : ℂ)⁻¹ := by
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((actionIndexEquiv k : ℕ) : ℝ) from Nat.cast_nonneg _),
      Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
  change (Coeff.insert positiveDirichletIndex _ (positiveDirichletIndex k)+
    Coeff.insert negativeDirichletIndex _ (positiveDirichletIndex k))/_ = _
  rw [Coeff.insert_apply_image,Coeff.insert_apply_outside _ _ _ (positiveDirichletIndex_not_mem_negative k),add_zero]
  change (-z.1 k-(2*I*(Real.pi : ℂ))*((actionIndexEquiv k : ℕ)/(1+(actionIndexEquiv k : ℕ) : ℂ)*z.2 k))/_ = _
  rw [hw]
  have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
  field_simp

theorem freeDirichletReconstruction_negative (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (freeDirichletReconstruction z).val.val (-(actionIndexEquiv k : ℤ)) =
      -(1+(actionIndexEquiv k : ℕ) : ℂ)*z.1 k+2*I*(Real.pi : ℂ)*(actionIndexEquiv k : ℕ)*z.2 k := by
  have hw : (Weight.sobolev (-1) (-(actionIndexEquiv k : ℤ)) : ℂ) =
      (1+(actionIndexEquiv k : ℕ) : ℂ)⁻¹ := by
    rw [Weight.sobolev_neg]
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((actionIndexEquiv k : ℕ) : ℝ) from Nat.cast_nonneg _),
      Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
  change (Coeff.insert positiveDirichletIndex _ (negativeDirichletIndex k)+
    Coeff.insert negativeDirichletIndex _ (negativeDirichletIndex k))/_ = _
  rw [Coeff.insert_apply_outside _ _ _ (negativeDirichletIndex_not_mem_positive k),Coeff.insert_apply_image,zero_add]
  change (-z.1 k+(2*I*(Real.pi : ℂ))*((actionIndexEquiv k : ℕ)/(1+(actionIndexEquiv k : ℕ) : ℂ)*z.2 k))/_ = _
  rw [hw]
  have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
  field_simp

def freeDirichletCombinedLinearization : PeriodOneMeanZeroHminusOne →L[ℂ] (Coeff 2 × Coeff 2) :=
  (freeNormalizedDirichletLinearization.prod freeDirichletLogNormingLinearization).comp periodOneMeanZeroInclusion

theorem freeDirichletCombinedLinearization_reconstruction (z : Coeff 2 × Coeff 2) :
    freeDirichletCombinedLinearization (freeDirichletReconstruction z) = z := by
  apply Prod.ext
  · ext k
    change freeNormalizedDirichletLinearization (freeDirichletReconstruction z).val k = _
    rw [freeNormalizedDirichletLinearization_apply,periodOneMeanZeroHminusOne_zero_coefficient,
      freeDirichletReconstruction_positive,freeDirichletReconstruction_negative]
    have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
    field_simp
    ring
  · ext k
    change freeDirichletLogNormingLinearization (freeDirichletReconstruction z).val k = _
    rw [freeDirichletLogNormingLinearization_apply,freeDirichletReconstruction_positive,freeDirichletReconstruction_negative]
    have hn : (actionIndexEquiv k : ℂ) ≠ 0 := by exact_mod_cast (actionIndexEquiv k).ne_zero
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring

theorem freeDirichletReconstruction_combinedLinearization (q : PeriodOneMeanZeroHminusOne) :
    freeDirichletReconstruction (freeDirichletCombinedLinearization q) = q := by
  have hpos (k : ℤ) : (freeDirichletReconstruction (freeDirichletCombinedLinearization q)).val.val (actionIndexEquiv k : ℤ) =
      q.val.val (actionIndexEquiv k : ℤ) := by
    rw [freeDirichletReconstruction_positive]
    change -(1+(actionIndexEquiv k : ℕ) : ℂ)*(freeNormalizedDirichletLinearization q.val k)-
      2*I*(Real.pi : ℂ)*(actionIndexEquiv k : ℕ)*(freeDirichletLogNormingLinearization q.val k) = _
    rw [freeNormalizedDirichletLinearization_apply,freeDirichletLogNormingLinearization_apply,periodOneMeanZeroHminusOne_zero_coefficient q]
    have hn : (actionIndexEquiv k : ℂ) ≠ 0 := by exact_mod_cast (actionIndexEquiv k).ne_zero
    have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  have hneg (k : ℤ) : (freeDirichletReconstruction (freeDirichletCombinedLinearization q)).val.val (-(actionIndexEquiv k : ℤ)) =
      q.val.val (-(actionIndexEquiv k : ℤ)) := by
    rw [freeDirichletReconstruction_negative]
    change -(1+(actionIndexEquiv k : ℕ) : ℂ)*(freeNormalizedDirichletLinearization q.val k)+
      2*I*(Real.pi : ℂ)*(actionIndexEquiv k : ℕ)*(freeDirichletLogNormingLinearization q.val k) = _
    rw [freeNormalizedDirichletLinearization_apply,freeDirichletLogNormingLinearization_apply,periodOneMeanZeroHminusOne_zero_coefficient q]
    have hn : (actionIndexEquiv k : ℂ) ≠ 0 := by exact_mod_cast (actionIndexEquiv k).ne_zero
    have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rcases lt_trichotomy j 0 with hj | hj | hj
  · let n : ℕ+ := ⟨(-j).toNat,by omega⟩
    have hn : (actionIndexEquiv (actionIndexEquiv.symm n) : ℤ) = -j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg (by omega)
    simpa only [hn,neg_neg] using hneg (actionIndexEquiv.symm n)
  · subst j
    exact (freeDirichletReconstructionRaw_zero _).trans q.property.symm
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (actionIndexEquiv (actionIndexEquiv.symm n) : ℤ) = j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg hj.le
    simpa only [hn] using hpos (actionIndexEquiv.symm n)

def freeDirichletFourierEquiv : PeriodOneMeanZeroHminusOne ≃L[ℂ] (Coeff 2 × Coeff 2) where
  toLinearEquiv :=
    { toLinearMap := freeDirichletCombinedLinearization.toLinearMap
      invFun := freeDirichletReconstruction
      left_inv := freeDirichletReconstruction_combinedLinearization
      right_inv := freeDirichletCombinedLinearization_reconstruction }
  continuous_toFun := freeDirichletCombinedLinearization.continuous
  continuous_invFun := freeDirichletReconstruction.continuous

end NLS.Articles.KdVConvexity
