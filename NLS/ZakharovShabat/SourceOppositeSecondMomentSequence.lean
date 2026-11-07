import NLS.ZakharovShabat.SourceNormalizedSecondMomentAnalytic
import NLS.ZakharovShabat.SourceAbelianMomentCubicCoefficients
import NLS.ZakharovShabat.SourceComplexOpenGapDensity
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.PuncturedLattice

/-! The normalized moment at the opposite own label is an analytic
Hilbert packet. A reciprocal index factor controls every coordinate,
including limits across collapsed opposite gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W V R : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem exists_ball_opposite_secondMoment_l2
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) R s)
    (D : SourceAbelianMomentErrorDomain A) (φ : realTypeSourceSubmodule 2)
    (hφV : φ.val∈V) (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0<r ∧ ball φ.val r⊆D.domain∩V∩ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ K : ℝ, 0≤K ∧ ∃ G : CoeffPair 2 → Coeff 2,
        AnalyticOnNhd ℂ G (ball φ.val r) ∧
        (∀ ψ∈ball φ.val r, ∀ n : ℤ, G ψ n=if n=0 then 0 else C.normalizedSecondMoment s n (-n) ψ) ∧
        (∀ ψ∈ball φ.val r, ∀ n : ℤ,
          ‖G ψ n‖≤K*‖Coeff.puncturedLattice 2 (by norm_num) n‖) ∧
        ∀ ψ∈ball φ.val r, ‖G ψ‖≤K*‖Coeff.puncturedLattice 2 (by norm_num)‖ := by
  obtain ⟨T,hT,hφT,hTD,hcoeff⟩ := D.exists_local_offDiagonal_secondMoment_coefficients hs φ hφV
  obtain ⟨M,hM,hrows⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨a,ha,hasub,hNa⟩ := C.exists_ball_normalizedSecondMoments
    hs.toSourcePsiIsolatingComplexExtension hV φ hφV hφC
  obtain ⟨Q,hQ,_hQc,hrealQ,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨_N,_hN,L,hL,hφL,B,hB,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) φ.val (by norm_num : (0 : ℝ)<1)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((((hT.inter isOpen_ball).inter hQ).inter hL).mem_nhds
      ⟨⟨⟨hφT,mem_ball_self ha⟩,hrealQ φ.property⟩,hφL⟩)
  let U := ball φ.val r
  let K := B*M
  have hK : 0≤K := mul_nonneg hB hM
  let P := Coeff.puncturedLattice 2 (by norm_num)
  let f := fun ψ n => if n=0 then (0 : ℂ) else C.normalizedSecondMoment s n (-n) ψ
  have hUD (ψ : CoeffPair 2) (hψ : ψ∈U) : ψ∈D.domain := (hTD (hsub hψ).1.1.1).1
  have hUC (ψ : CoeffPair 2) (hψ : ψ∈U) : ψ∈ball C.discs.source.val C.discs.sourceRadius :=
    (hasub (hsub hψ).1.1.2).2
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) U := by
    by_cases hn : n=0
    · simpa only [f,if_pos hn] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
    · simpa only [f,if_neg hn] using (hNa n (-n)).mono (fun ψ hψ => (hsub hψ).1.1.2)
  have hγ (n : ℤ) : AnalyticOnNhd ℂ (fun ψ =>
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n)^2) U := by
    intro ψ hψ
    simpa only [sourcePeriodicGapDisplacement_apply] using (hcoord ψ (hsub hψ).1.2 n).2
  have hopenBound (ψ : CoeffPair 2) (hψ : ψ∈U) (n : ℤ)
      (hg : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-n)≠0) :
      ‖f ψ n‖≤K*‖P n‖ := by
    by_cases hn : n=0
    · simp only [f,if_pos hn,norm_zero]
      exact mul_nonneg hK (norm_nonneg _)
    have hkn : -n≠n := by omega
    obtain ⟨b,_hb,_hbn,hbnorm,hfactor⟩ := hrows ψ (hsub hψ).1.1.1 n
    have hden : (((n-(-n) : ℤ) : ℂ))≠0 := by exact_mod_cast (show n-(-n)≠0 by omega)
    have hc := C.moment_two_eq_squaredGap_mul_normalized A D ψ (hUD ψ hψ) (hUC ψ hψ) n (-n)
    have he := hc.symm.trans (hfactor (-n) hkn)
    field_simp [hden] at he
    have hrel : (((n-(-n) : ℤ) : ℂ)*C.normalizedSecondMoment s n (-n) ψ)=
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-n)*b (-n) := by
      linear_combination he
    have hdn : ‖(((n-(-n) : ℤ) : ℂ))‖=2*|(n : ℝ)| := by
      rw [show n-(-n)=2*n by ring,Complex.norm_intCast]
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have hnorm := congrArg norm hrel
    rw [norm_mul,hdn,norm_mul] at hnorm
    have hgn : ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-n)‖≤B :=
      (lp.norm_apply_le_norm (by norm_num) _ _).trans (hgap ψ (hsub hψ).2).1
    have hbn : ‖b (-n)‖≤M := (lp.norm_apply_le_norm (by norm_num) b (-n)).trans hbnorm
    have hprod := mul_le_mul hgn hbn (norm_nonneg _) hB
    have hpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    rw [show f ψ n=C.normalizedSecondMoment s n (-n) ψ from if_neg hn]
    simp only [P,Coeff.puncturedLattice_apply,if_neg hn,norm_inv,Complex.norm_intCast]
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ hpos).mpr
    dsimp only [K] at *
    nlinarith [mul_nonneg hpos.le (norm_nonneg (C.normalizedSecondMoment s n (-n) ψ))]
  have hpoint (ψ : CoeffPair 2) (hψ : ψ∈U) (n : ℤ) : ‖f ψ n‖≤K*‖P n‖ := by
    have hd := subset_closure_complex_finite_open_gaps
      (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) U isOpen_ball
      ⟨⟨φ.val,mem_ball_self hr⟩,(convex_ball φ.val r).isPreconnected⟩ φ (mem_ball_self hr) hγ {-n}
    obtain ⟨y,hy,ht⟩ := mem_closure_iff_seq_limit.mp (hd hψ)
    apply le_of_tendsto ((((hf n).continuousOn.continuousAt (isOpen_ball.mem_nhds hψ)).tendsto.comp ht).norm)
    exact Filter.Eventually.of_forall (fun i => hopenBound (y i) (hy i).1 n ((hy i).2 (-n) (Finset.mem_singleton_self _)))
  let Z : Coeff 2 := (K : ℂ) • Coeff.magnitude P
  have hZn (n : ℤ) : ‖Z n‖=K*‖P n‖ := by
    simp only [Z,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hK,
      Coeff.magnitude_apply,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  have hb (ψ : CoeffPair 2) (hψ : ψ∈U) : ∃ b : Coeff 2,
      (∀ n, b n=f ψ n) ∧ ‖b‖≤K*‖P‖ := by
    have hp (n : ℤ) : ‖f ψ n‖≤‖Z n‖ := by rw [hZn]; exact hpoint ψ hψ n
    let b : Coeff 2 := ⟨f ψ,(lp.memℓp Z).mono' hp⟩
    refine ⟨b,fun _ => rfl,(lp.norm_mono (by norm_num) hp).trans ?_⟩
    simp only [Z,norm_smul,Complex.norm_real,Real.norm_of_nonneg hK,Coeff.norm_magnitude,le_refl]
  obtain ⟨hval,hG⟩ := Coeff.analytic_realization_of_local_bounds (r := 2) f isOpen_ball hf
    (fun ψ hψ => ⟨U,isOpen_ball,hψ,Subset.refl _,K*‖P‖,hb⟩)
  refine ⟨r,hr,fun ψ hψ => ⟨hTD (hsub hψ).1.1.1,hUC ψ hψ⟩,K,hK,
    (fun ψ => Coeff.ofFunctionOrZero 2 (f ψ)),hG,hval,?_,?_⟩
  · intro ψ hψ n
    change ‖Coeff.ofFunctionOrZero 2 (f ψ) n‖≤K*‖P n‖
    rw [hval ψ hψ n]
    exact hpoint ψ hψ n
  · intro ψ hψ
    obtain ⟨b,hb,hbn⟩ := hb ψ hψ
    change ‖Coeff.ofFunctionOrZero 2 (f ψ)‖≤K*‖P‖
    rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
