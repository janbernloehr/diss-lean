import NLS.SequenceSpaces.PeriodOneFourierLebesgueFreeMassEquiv
import NLS.SequenceSpaces.PhysicalPositiveMultiplierEquiv
import NLS.SequenceSpaces.SignChange
import NLS.SequenceSpaces.HolderEmbedding

/-! # Exact free-mass weighted positive principal equivalence

The eta symbol, physical packet symbol, signs and mass resolvent are
combined in the original real weighted lp spaces. Reciprocals are only
needed on positive indices for the physical packet factor.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

def periodOneMassBracketRatio (m : ℕ) : Coeff ⊤ :=
  ⟨fun n => (Weight.sobolev 1 n : ℂ)*(periodOneMassSymbol m n)⁻¹,
    memℓp_infty ⟨2,by
      rintro _ ⟨n,rfl⟩
      change ‖(Weight.sobolev 1 n : ℂ)*(periodOneMassSymbol m n)⁻¹‖≤2
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ n)]
      have h := periodOneMassSymbol_weighted_inverse_bound m 0 n
      simpa only [zero_add,Weight.sobolev_zero_apply,mul_one,one_mul] using h⟩⟩

def periodOneMassBracketInverseRatio (m : ℕ) : Coeff ⊤ :=
  ⟨fun n => periodOneMassSymbol m n/(Weight.sobolev 1 n : ℂ),
    memℓp_infty ⟨(m : ℝ)+1+2*Real.pi,by
      rintro _ ⟨n,rfl⟩
      change ‖periodOneMassSymbol m n/(Weight.sobolev 1 n : ℂ)‖≤(m : ℝ)+1+2*Real.pi
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ n)]
      apply (div_le_iff₀ (Weight.positive _ n)).mpr
      simpa only [Weight.sobolev_apply,Real.rpow_one] using norm_periodOneMassSymbol_le_linear m n⟩⟩

theorem periodOneMassBracketRatio_inverse (m : ℕ) (n : ℤ) :
    periodOneMassBracketRatio m n*periodOneMassBracketInverseRatio m n=1 := by
  change (Weight.sobolev 1 n : ℂ)*(periodOneMassSymbol m n)⁻¹*
    (periodOneMassSymbol m n/(Weight.sobolev 1 n : ℂ))=1
  field_simp [periodOneMassSymbol_ne_zero m n]
  exact div_self ((Weight.sobolev 1).complex_ne_zero n)

def fourierLebesguePrincipalSymbol (σ τ : Coeff ⊤) (signs : ℤ → Bool) : Coeff ⊤ :=
  (2*I) • Coeff.signChange signs
    (Coeff.holderProduct (q := ⊤) τ (Coeff.holderProduct (q := ⊤) σ (periodOneMassBracketRatio 0)))

def fourierLebesguePrincipalInverseSymbol (ν ρ : Coeff ⊤) (signs : ℤ → Bool) : Coeff ⊤ :=
  (2*I)⁻¹ • Coeff.signChange signs
    (Coeff.holderProduct (q := ⊤) ρ (Coeff.holderProduct (q := ⊤) ν (periodOneMassBracketInverseRatio 0)))

theorem fourierLebesguePrincipalSymbol_inverse
    (σ ν τ ρ : Coeff ⊤) (signs : ℤ → Bool)
    (hσν : ∀ n : ℤ, σ n*ν n=1) (hτρ : ∀ n : ℤ, 0<n → τ n*ρ n=1)
    (n : ℤ) (hn : 0<n) :
    fourierLebesguePrincipalSymbol σ τ signs n*fourierLebesguePrincipalInverseSymbol ν ρ signs n=1 := by
  have hmass := periodOneMassBracketRatio_inverse 0 n
  have heta := hσν n
  have hpacket := hτρ n hn
  simp only [fourierLebesguePrincipalSymbol,fourierLebesguePrincipalInverseSymbol,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.signChange_apply,Coeff.holderProduct_apply]
  cases signs n <;> simp only [Bool.false_eq_true,↓reduceIte]
    <;> calc
      _ = ((2*I)*(2*I)⁻¹)*(τ n*ρ n)*(σ n*ν n)*
        (periodOneMassBracketRatio 0 n*periodOneMassBracketInverseRatio 0 n) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ (by simp : (2*I : ℂ)≠0),hmass,heta,hpacket]; norm_num

def physicalFourierLebesguePrincipalEquiv (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (σ ν τ ρ : Coeff ⊤) (signs : ℤ → Bool)
    (hσν : ∀ n : ℤ, σ n*ν n=1) (hτρ : ∀ n : ℤ, 0<n → τ n*ρ n=1) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃L[ℝ]
      physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p :=
  WeightedCoeff.physicalPositiveMultiplierEquiv _ _ p
    (fun n => by simp only [Weight.sobolev_apply,Int.cast_neg,abs_neg])
    (fun n => by simp only [Weight.sobolev_apply,Int.cast_neg,abs_neg])
    (fourierLebesguePrincipalSymbol σ τ signs)
    (fourierLebesguePrincipalInverseSymbol ν ρ signs)
    (fourierLebesguePrincipalSymbol_inverse σ ν τ ρ signs hσν hτρ)

def fourierLebesgueComplexPrincipal (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (σ τ : Coeff ⊤) (signs : ℤ → Bool) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] Coeff p :=
  (Coeff.signChange signs).comp
    ((Coeff.holderProduct (q := p) τ).comp
      (((Coeff.holderProduct (q := p) σ).comp
        ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev (s+1)) p).toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (periodOneFourierLebesgueFreeMassEquiv 0 s p).symm.toContinuousLinearMap))

def physicalFourierLebesguePrincipal (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (σ τ : Coeff ⊤) (signs : ℤ → Bool) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p →L[ℝ]
      physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p :=
  (WeightedCoeff.physicalPositiveRealLift _ p (Weight.sobolev_neg (s+1/2))).comp
    (((fourierLebesgueComplexPrincipal s p σ τ signs).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p).subtypeL)

theorem physicalFourierLebesguePrincipalEquiv_toContinuousLinearMap
    (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (σ ν τ ρ : Coeff ⊤) (signs : ℤ → Bool)
    (hσν : ∀ n : ℤ, σ n*ν n=1) (hτρ : ∀ n : ℤ, 0<n → τ n*ρ n=1) :
    (physicalFourierLebesguePrincipalEquiv s p σ ν τ ρ signs hσν hτρ).toContinuousLinearMap=
      physicalFourierLebesguePrincipal s p σ τ signs := by
  apply ContinuousLinearMap.ext
  intro a
  apply physicalRealMeanZeroWeightedExponent_ext_positive
  intro n hn
  change (WeightedCoeff.physicalPositiveMultiplier _ _ p (Weight.sobolev_neg (s+1/2))
    (fourierLebesguePrincipalSymbol σ τ signs) a).val.val n=
      (WeightedCoeff.physicalPositiveRealLift _ p (Weight.sobolev_neg (s+1/2))
        (fourierLebesgueComplexPrincipal s p σ τ signs a.val)).val.val n
  rw [WeightedCoeff.physicalPositiveMultiplier_apply_positive _ _ p _ _ a n hn,
    WeightedCoeff.physicalPositiveRealLift_apply,if_pos hn,
    if_neg (by omega : ¬0< -n),map_zero,add_zero]
  change _=(Coeff.signChange signs (Coeff.holderProduct (q := p) τ
    (Coeff.holderProduct (q := p) σ ((2*I) •
      (WeightedCoeff.weightIsometry (Weight.sobolev (s+1)) p)
        (periodOneFourierLebesgueMassInverse 0 s p a.val))))) n/_
  simp only [fourierLebesguePrincipalSymbol,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    Coeff.signChange_apply,Coeff.holderProduct_apply]
  change (2*I)*(if signs n then -(τ n*(σ n*periodOneMassBracketRatio 0 n)) else
    τ n*(σ n*periodOneMassBracketRatio 0 n))*((Weight.sobolev s n : ℂ)*a.val.val n)/_=
    (if signs n then -(τ n*(σ n*((2*I)*((Weight.sobolev (s+1) n : ℂ)*
      ((periodOneMassSymbol 0 n)⁻¹*a.val.val n))))) else
    τ n*(σ n*((2*I)*((Weight.sobolev (s+1) n : ℂ)*
      ((periodOneMassSymbol 0 n)⁻¹*a.val.val n)))))/_
  have hw : (Weight.sobolev (s+1) n : ℂ)=
      (Weight.sobolev s n : ℂ)*(Weight.sobolev 1 n : ℂ) := by
    rw [Weight.sobolev_add,ofReal_mul]
  change (2*I)*(if signs n then -(τ n*(σ n*((Weight.sobolev 1 n : ℂ)*(periodOneMassSymbol 0 n)⁻¹))) else
    τ n*(σ n*((Weight.sobolev 1 n : ℂ)*(periodOneMassSymbol 0 n)⁻¹)))*((Weight.sobolev s n : ℂ)*a.val.val n)/_=_
  rw [hw]
  cases signs n <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring

end NLS
