import NLS.ZakharovShabat.SourceRegularDiagonalActionCancellation
import NLS.ZakharovShabat.SourceAbelianMomentDiagonalCoefficients
import NLS.ZakharovShabat.SourceComplexOpenGapDensity
import NLS.SequenceSpaces.DenseFiniteHilbertBounds

/-! The actual regular diagonal moment error is a bounded analytic
Hilbert packet on a full complex neighborhood. Finite coordinate bounds
extend across closed gaps before constructing the sequence. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W V R : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem exists_ball_regularDiagonal_error_l2
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V)
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) R s)
    (D : SourceAbelianMomentErrorDomain A) (φ : realTypeSourceSubmodule 2)
    (hφV : φ.val∈V) (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0<r ∧ ball φ.val r⊆D.domain∩V∩ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ M : ℝ, 0≤M ∧ ∃ G : CoeffPair 2 → Coeff 2,
        AnalyticOnNhd ℂ G (ball φ.val r) ∧
        (∀ ψ∈ball φ.val r, ∀ n : ℤ, G ψ n=C.regularDiagonalSecondMomentError s n ψ) ∧
        ∀ ψ∈ball φ.val r, ‖G ψ‖≤M := by
  obtain ⟨T,hT,hφT,hTD,hcoeff⟩ := D.exists_local_diagonal_secondMoment_coefficients hs φ hφV
  obtain ⟨M,hM,hrows⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨a,ha,hasub,hNa⟩ := C.exists_ball_normalizedSecondMoments
    hs.toSourcePsiIsolatingComplexExtension hV φ hφV hφC
  obtain ⟨Q,hQ,_hQc,hrealQ,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (((hT.inter isOpen_ball).inter hQ).mem_nhds ⟨⟨hφT,mem_ball_self ha⟩,hrealQ φ.property⟩)
  let U := ball φ.val r
  have hUD (ψ : CoeffPair 2) (hψ : ψ∈U) : ψ∈D.domain := (hTD (hsub hψ).1.1).1
  have hUC (ψ : CoeffPair 2) (hψ : ψ∈U) : ψ∈ball C.discs.source.val C.discs.sourceRadius :=
    (hasub (hsub hψ).1.2).2
  let f := fun ψ n => C.regularDiagonalSecondMomentError s n ψ
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) U :=
    (analyticOnNhd_const.mul ((hNa n n).mono (fun ψ hψ => (hsub hψ).1.2))).sub analyticOnNhd_const
  have hγ (n : ℤ) : AnalyticOnNhd ℂ (fun ψ =>
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n)^2) U := by
    intro ψ hψ
    simpa only [sourcePeriodicGapDisplacement_apply] using (hcoord ψ (hsub hψ).2 n).2
  have hd (S : Finset ℤ) := subset_closure_complex_finite_open_gaps
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) U isOpen_ball
    ⟨⟨φ.val,mem_ball_self hr⟩,(convex_ball φ.val r).isPreconnected⟩ φ (mem_ball_self hr) hγ S
  have hb (ψ : CoeffPair 2) (hψ : ψ∈U) :
      ∃ b : Coeff 2, (∀ n, b n=f ψ n) ∧ ‖b‖≤M := by
    apply Coeff.exists_l2_of_dense_finite_coordinate_bounds U isOpen_ball f
      (fun n => (hf n).continuousOn) M hM ?_ ψ hψ
    intro S
    apply (hd S).trans
    apply closure_mono
    rintro χ ⟨hχ,hopen⟩
    obtain ⟨b,_hb,hbn,hfactor⟩ := hrows χ (hsub hχ).1.1
    refine ⟨hχ,b,hbn,?_⟩
    intro n hn
    have hc := C.moment_two_eq_squaredGap_mul_normalized A D χ (hUD χ hχ) (hUC χ hχ) n n
    have he : (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) χ n)^2*
        C.regularDiagonalSecondMomentError s n χ =
        (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) χ n)^2*b n := by
      unfold regularDiagonalSecondMomentError
      linear_combination 4*(hfactor n)-4*hc
    exact (mul_left_cancel₀ (pow_ne_zero 2 (hopen n hn)) he).symm
  obtain ⟨hval,hG⟩ := Coeff.analytic_realization_of_local_bounds (r := 2) f isOpen_ball hf
    (fun ψ hψ => ⟨U,isOpen_ball,hψ,Subset.refl _,M,hb⟩)
  refine ⟨r,hr,fun ψ hψ => ⟨hTD (hsub hψ).1.1,hUC ψ hψ⟩,M,hM,
    (fun ψ => Coeff.ofFunctionOrZero 2 (f ψ)),hG,hval,?_⟩
  intro ψ hψ
  obtain ⟨b,hb,hbn⟩ := hb ψ hψ
  change ‖Coeff.ofFunctionOrZero 2 (f ψ)‖≤M
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
