import NLS.KdV.HillActionPreservingCurves
import NLS.KdV.HillOriginalBirkhoffMap
import NLS.SequenceSpaces.ComplexHilbertPhaseFiber

/-! # The complete original Hill actions determine the discriminant

Pull single-mode phase rotations through the ACTUAL globally real analytic
original inverse. Their full original actions remain constant; the complete
action-kernel theorem therefore gives actual isospectrality. Norm limits
of finite rotations cover arbitrary equal-magnitude Hilbert sequences.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Exact physical action normalization of the original global spectral
sequence, including every low and closed gap. -/
theorem norm_hillOriginalMeanZeroRealSpectralMap_coordinate_sq
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    ‖hillOriginalMeanZeroRealSpectralMap q k‖^2=
      (4*Real.pi*(k+1 : ℕ))*hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 := by
  change ‖hillOriginalBaseSpectralSequence (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential) k‖^2=_
  rw [hillOriginalBaseSpectralSequence_apply,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity)]
  have hc : ‖hillSignedSpectralCartesian true ⟨k+1,by omega⟩
      (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential)‖^2=
      2*hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simpa only [hillSignedSpectralCartesian,ite_true,pow_two] using!
      hillSpectralCartesian_action_identity (by simp) (by intro j; simp)
        q.val.val q.val.property.1 q.val.property.2 (k+1) (by omega)
  rw [hc]
  ring

theorem norm_hillOriginalInverse_coordinate_sq
    (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) :
    ‖z k‖^2=(4*Real.pi*(k+1 : ℕ))*
      hillRealGapIntegral (hillOriginalMeanZeroSpectralInverse z).val.val
        (hillOriginalMeanZeroSpectralInverse z).val.property.1
        (hillOriginalMeanZeroSpectralInverse z).val.property.2 (k+1) 0 := by
  have h := norm_hillOriginalMeanZeroRealSpectralMap_coordinate_sq (hillOriginalMeanZeroSpectralInverse z) k
  rwa [hillOriginalMeanZeroRealSpectralMap_apply_inverse] at h

/-- A genuine single-coordinate phase rotation pulled through the SAME
actual original inverse preserves EVERY original Hill action. -/
theorem hillOriginalInverse_rotate_actions
    (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) (t : ℝ) (n : ℕ+) :
    let p := hillOriginalMeanZeroSpectralInverse (ComplexHilbert.rotate z k t)
    let q := hillOriginalMeanZeroSpectralInverse z
    hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0=
      hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0 := by
  intro p q
  have hn : (n : ℕ)-1+1=(n : ℕ) := by have := n.pos; omega
  have hp := norm_hillOriginalInverse_coordinate_sq (ComplexHilbert.rotate z k t) ((n : ℕ)-1)
  have hq := norm_hillOriginalInverse_coordinate_sq z ((n : ℕ)-1)
  rw [ComplexHilbert.norm_rotate_coordinate] at hp
  rw [hn] at hp hq
  have hc : 0<4*Real.pi*(n : ℕ) := by have := n.pos; positivity
  change _ = _
  nlinarith [hp,hq]

/-- Every actual original inverse phase curve is isospectral at EVERY
complex energy, with infinite support and arbitrary-size data allowed. -/
theorem hillOriginalInverse_rotate_discriminant
    (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) (t : ℝ) (E : ℂ) :
    hillL2Discriminant (hillMeanZeroSourceCoeff
        (hillOriginalMeanZeroSpectralInverse (ComplexHilbert.rotate z k t))) E=
      hillL2Discriminant (hillMeanZeroSourceCoeff (hillOriginalMeanZeroSpectralInverse z)) E := by
  let γ := fun τ => hillOriginalMeanZeroSpectralInverse (ComplexHilbert.rotate z k τ)
  have hγ : Differentiable ℝ γ := by
    intro τ
    exact (analyticOnNhd_hillOriginalMeanZeroSpectralInverse _ (mem_univ _)).differentiableAt.comp τ
      (ComplexHilbert.hasDerivAt_rotate z k τ).differentiableAt
  have hI (n : ℕ+) (τ : ℝ) :
      hillRealGapIntegral (γ τ).val.val (γ τ).val.property.1 (γ τ).val.property.2 n 0=
        hillRealGapIntegral (γ 0).val.val (γ 0).val.property.1 (γ 0).val.property.2 n 0 := by
    simpa only [γ,ComplexHilbert.rotate_zero] using hillOriginalInverse_rotate_actions z k τ n
  simpa only [γ,ComplexHilbert.rotate_zero] using
    hillDiscriminant_eq_on_action_preserving_curve γ hγ hI E t 0

/-- The full ACTUAL discriminant of the SAME global original inverse
is determined by the complete Hilbert coordinate magnitudes. -/
theorem hillOriginalInverse_discriminant_eq_of_coordinate_norm_eq
    (z w : lp (fun _ : ℕ => ℂ) 2) (h : ∀ k, ‖z k‖=‖w k‖) (E : ℂ) :
    hillL2Discriminant (hillMeanZeroSourceCoeff (hillOriginalMeanZeroSpectralInverse z)) E=
      hillL2Discriminant (hillMeanZeroSourceCoeff (hillOriginalMeanZeroSpectralInverse w)) E := by
  let f := fun a => hillL2Discriminant (hillMeanZeroSourceCoeff (hillOriginalMeanZeroSpectralInverse a)) E
  have hD : Continuous (fun a : Coeff 2 => hillL2Discriminant a E) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    have ha := (analyticOnNhd_hillL2Discriminant_joint (E,a) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
    exact ha.continuousAt
  have hf : Continuous f := hD.comp
    (hillMeanZeroSourceCoeff.continuous.comp continuous_hillOriginalMeanZeroSpectralInverse)
  exact ComplexHilbert.eq_of_coordinate_norm_eq f hf
    (fun a k t => hillOriginalInverse_rotate_discriminant a k t E) z w h

/-- Equal COMPLETE original actions imply equality of the ACTUAL entire
Hill discriminants on the original real mean-zero L2 space. This is a
proved global action-fiber statement, including ALL closed gaps. -/
theorem hillOriginalDiscriminant_eq_of_actions_eq
    (q p : hillRealMeanZeroSourceSubmodule)
    (h : ∀ n : ℕ+, hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 n 0=
      hillRealGapIntegral p.val.val p.val.property.1 p.val.property.2 n 0) (E : ℂ) :
    hillL2Discriminant (hillMeanZeroSourceCoeff q) E=hillL2Discriminant (hillMeanZeroSourceCoeff p) E := by
  have hn (k : ℕ) : ‖hillOriginalMeanZeroRealSpectralMap q k‖=‖hillOriginalMeanZeroRealSpectralMap p k‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_hillOriginalMeanZeroRealSpectralMap_coordinate_sq,
      norm_hillOriginalMeanZeroRealSpectralMap_coordinate_sq]
    exact congrArg (fun r : ℝ => (4*Real.pi*(k+1 : ℕ))*r) (h ⟨k+1,by omega⟩)
  have he := hillOriginalInverse_discriminant_eq_of_coordinate_norm_eq
    (hillOriginalMeanZeroRealSpectralMap q) (hillOriginalMeanZeroRealSpectralMap p) hn E
  simpa only [hillOriginalMeanZeroSpectralInverse_apply_map] using he

end NLS.KdV
