import NLS.ZakharovShabat.SourceBirkhoffCoordinates

/-! # Uniform bounds for the rectangular coordinates

The action-root deviation controls every root by one constant.
Uniform eta and beta bounds then give the same spectral majorant for
both rectangular coordinates, with no open-gap assumption.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_uniform_sourceNormalizedActionRoot_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ A : ℝ, 0 < A ∧ ∀ ψ ∈ U, ∀ n : ℤ, ‖sourceNormalizedActionRoot hp hp1 n ψ‖ ≤ A := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨U,hU,hφU,M,F,hF,hbound,_,_⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap (q := p) hp hp1 hp1 hp hhalf φ hreal
  have hM : 0 ≤ M := (norm_nonneg (F φ)).trans (hbound φ hφU)
  refine ⟨U,hU,hφU,M+1,by linarith,?_⟩
  intro ψ hψ n
  have hξ : sourceNormalizedActionRoot hp hp1 n ψ = F ψ n+1 := by
    rw [hF ψ hψ n,sourceNormalizedActionRootDeviation,sub_add_cancel]
  rw [hξ]
  exact (norm_add_le _ _).trans (by
    rw [norm_one]
    exact add_le_add ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (F ψ) n).trans (hbound ψ hψ)) le_rfl)

/-- A scalar bound for each signed weighted phase. -/
theorem norm_sourceBirkhoffWeightedCoordinate_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (sign : ℂ) (hsign : ‖sign‖ ≤ 1) (A B C L : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hξ : ‖sourceNormalizedActionRoot hp hp1 n ψ‖ ≤ A)
    (hβ : ‖sourceAngularBetaCorrection hp hp1 n s ψ‖ ≤ B)
    (hz : ‖sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ‖ ≤ C*L) :
    ‖sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ‖ ≤ (A*C*Real.exp B)*L := by
  have he : ‖Complex.exp (sign*I*sourceAngularBetaCorrection hp hp1 n s ψ)‖ ≤ Real.exp B := by
    apply (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul,norm_mul,norm_I,mul_one]
    exact (mul_le_mul_of_nonneg_right hsign (norm_nonneg _)).trans (by simpa using hβ)
  rw [sourceBirkhoffWeightedCoordinate,norm_mul,norm_mul]
  calc
    _ ≤ (A*(C*L))*Real.exp B :=
      mul_le_mul (mul_le_mul hξ hz (norm_nonneg _) hA) he (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Both rectangular coordinates inherit the same gap/displacement
majorant from the two signed eta coordinates. -/
theorem norm_sourceBirkhoffXY_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (A B C L : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hξ : ‖sourceNormalizedActionRoot hp hp1 n ψ‖ ≤ A)
    (hβ : ‖sourceAngularBetaCorrection hp hp1 n s ψ‖ ≤ B)
    (hz : ∀ sign : ℂ, ‖sign‖ ≤ 1 → ‖sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ‖ ≤ C*L) :
    ‖sourceBirkhoffX hp hp1 n s ψ‖ ≤ (2*A*C*Real.exp B)*L ∧
      ‖sourceBirkhoffY hp hp1 n s ψ‖ ≤ (2*A*C*Real.exp B)*L := by
  have hplus := norm_sourceBirkhoffWeightedCoordinate_le hp hp1 n s ψ 1 (by norm_num)
    A B C L hA hC hL hξ hβ (hz 1 (by norm_num))
  have hminus := norm_sourceBirkhoffWeightedCoordinate_le hp hp1 n s ψ (-1) (by norm_num)
    A B C L hA hC hL hξ hβ (hz (-1) (by norm_num))
  have hd : 1 ≤ Real.sqrt 8 := (Real.one_le_sqrt).mpr (by norm_num)
  have hd1 : 1 ≤ ‖(Real.sqrt 8 : ℂ)‖ := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hd
  have hd2 : 1 ≤ ‖(Real.sqrt 8 : ℂ)*I‖ := by simpa only [norm_mul,norm_I,mul_one] using hd1
  constructor
  · rw [sourceBirkhoffX,norm_div]
    apply (div_le_self (norm_nonneg _) hd1).trans
    have ht := norm_add_le (sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ)
      (sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ)
    nlinarith
  · rw [sourceBirkhoffY,norm_div]
    apply (div_le_self (norm_nonneg _) hd2).trans
    have ht := norm_sub_le (sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ)
      (sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ)
    nlinarith

end NLS.ZakharovShabat
