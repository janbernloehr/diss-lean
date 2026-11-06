import NLS.KdV.HillOriginalGlobalInverse

/-! # Exact actions of the actual original Hilbert spectral sequence -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV

/-- The literal original target normalization retains the physical Hill
action with the exact factor `4*pi*n`. Closed gaps are included. -/
theorem norm_hillOriginalMeanZeroRealSpectralMap_apply_sq
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    ‖hillOriginalMeanZeroRealSpectralMap q k‖^2 =
      (4*Real.pi*(k+1 : ℕ))*
        hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 := by
  change ‖hillOriginalBaseSpectralSequence (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential) k‖^2 = _
  rw [hillOriginalBaseSpectralSequence_apply]
  change ‖(Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*
    hillSpectralCartesian q.val.val q.val.property.1 q.val.property.2 (k+1) (by omega)‖^2 = _
  rw [norm_mul,mul_pow,norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity),
    norm_hillSpectralCartesian (by simp) (by intro j; simp)]
  have hn : 0 ≤ 2*hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 :=
    mul_nonneg (by norm_num) (by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even
        q.val.val q.val.property.1 q.val.property.2 (k+1) (by omega) 0)
  rw [Real.sq_sqrt hn]
  ring

theorem hillOriginalActions_eq_of_spectral_moduli
    (q p : hillRealMeanZeroSourceSubmodule)
    (h : ∀ k, ‖hillOriginalMeanZeroRealSpectralMap q k‖ =
      ‖hillOriginalMeanZeroRealSpectralMap p k‖) (n : ℕ+) :
    hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 =
      hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0 := by
  have hn : (n : ℕ)-1+1 = (n : ℕ) := Nat.sub_add_cancel n.pos
  have he := congrArg (fun x : ℝ => x^2) (h ((n : ℕ)-1))
  rw [norm_hillOriginalMeanZeroRealSpectralMap_apply_sq,
    norm_hillOriginalMeanZeroRealSpectralMap_apply_sq,hn] at he
  exact mul_left_cancel₀ (by positivity : 4*Real.pi*(n : ℕ) ≠ 0) he

theorem hillOriginalSpectral_moduli_eq_of_actions
    (q p : hillRealMeanZeroSourceSubmodule)
    (h : ∀ n : ℕ+, hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 =
      hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0) (k : ℕ) :
    ‖hillOriginalMeanZeroRealSpectralMap q k‖ = ‖hillOriginalMeanZeroRealSpectralMap p k‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_hillOriginalMeanZeroRealSpectralMap_apply_sq,
    norm_hillOriginalMeanZeroRealSpectralMap_apply_sq]
  exact congrArg (fun x : ℝ => (4*Real.pi*(k+1 : ℕ))*x) (h ⟨k+1,by omega⟩)

end NLS.KdV
