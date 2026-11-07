import NLS.KdV.HillOnIndexUniformEnergyBound
import NLS.KdV.HillActionAngleUniformBound

/-! The complete ACTUAL scalar Cartesian coordinates obey the original
energy-weight estimate divided by sqrt(n), locally on ONE complex native
source neighborhood BEFORE ALL n. All physical phases and amplitude
normalizations are included; no target sequence theorem is inferred. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem norm_hillHminusActionAngleXY_le_of_factor_bounds (n : ℕ+) (q : PeriodOneHminusOne)
    (M : ℝ) (hp : ‖hillHminusActionAngleFactorPlus n q‖ ≤ M)
    (hm : ‖hillHminusActionAngleFactorMinus n q‖ ≤ M) :
    ‖hillHminusActionAngleX n q‖ ≤ M ∧ ‖hillHminusActionAngleY n q‖ ≤ M := by
  constructor
  · rw [hillHminusActionAngleX,norm_div,Complex.norm_ofNat]
    have h := norm_add_le (hillHminusActionAngleFactorPlus n q) (hillHminusActionAngleFactorMinus n q)
    linarith
  · rw [hillHminusActionAngleY,norm_div,norm_mul,Complex.norm_ofNat,norm_I,mul_one]
    have h := norm_sub_le (hillHminusActionAngleFactorPlus n q) (hillHminusActionAngleFactorMinus n q)
    linarith

theorem exists_local_uniform_actionAngle_original_energy_bound (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionAngleFactorPlus n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleFactorMinus n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleX n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleY n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨Ud,hUd,hqd,_,Cd,hCd,hdiag⟩ := P.exists_local_uniform_physicalOnIndexCartesian_original_energy_bound HP q hq hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q hq hr
  obtain ⟨Ua,hUa,hqa,hUaD,Ca,hCa,hamp⟩ := exists_local_uniform_actionAngle_diagonal_bound q
    (real_mem_hillHminusActionAmplitudeDomain q hr)
  let U := (Ud ∩ ball q r) ∩ Ua
  refine ⟨U,(hUd.inter isOpen_ball).inter hUa,⟨⟨hqd,mem_ball_self hrpos⟩,hqa⟩,
    (fun _ h => hUaD h.2),Ca*Cd,mul_pos hCa hCd,?_⟩
  intro y hy n
  have hd := hdiag y hy.1.1 n
  have ha := hamp y hy.2 n
  have he := heq n y hy.1.2
  rw [he.1,he.2] at ha
  have hCa' : 0 ≤ Ca/Real.sqrt (n:ℕ) := div_nonneg hCa.le (Real.sqrt_nonneg _)
  have hp : ‖hillHminusActionAngleFactorPlus n y‖ ≤
      ((Ca*Cd)/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y :=
    ha.1.trans (by
      have h := mul_le_mul_of_nonneg_left hd.1 hCa'
      convert h using 1; ring)
  have hm : ‖hillHminusActionAngleFactorMinus n y‖ ≤
      ((Ca*Cd)/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y :=
    ha.2.trans (by
      have h := mul_le_mul_of_nonneg_left hd.2 hCa'
      convert h using 1; ring)
  exact ⟨hp,hm,norm_hillHminusActionAngleXY_le_of_factor_bounds n y _ hp hm⟩

end NLS.KdV
