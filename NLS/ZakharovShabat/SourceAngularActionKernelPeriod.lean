import NLS.ComplexAnalysis.BoundedUniformMultiplier
import NLS.ZakharovShabat.SourcePsiDirichletInterpolation
import NLS.ZakharovShabat.SourceAngularEtaActionKernel

/-! # Transporting the actual action kernel sum to a psi period

Uniform actual Dirichlet interpolation on the action circle allows
integration term by term through the symmetric cutoffs. The literal
kernel normalization and spectral orientation give the normalized
psi period, including when any Dirichlet terminal is a branch.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized terminal kernel sum converges to the actual
normalized psi period on every action chart, for finite `p > 1`. -/
theorem tendsto_sourcePsiDirichlet_actionKernelSums
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : Coeff p)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ ball ch.center ch.radius) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,a)*
        sourceDirichletActionKernel hp hp1 m k ch φ.val) atTop
      (𝓝 ((2*Real.pi : ℂ)⁻¹*(∮ w in C(ch.spectralCenter,ch.spectralRadius),
        sourcePsiContourIntegrandJoint hp hp1 n (w,(a,φ.val))))) := by
  let c := ch.spectralCenter
  let R := ch.spectralRadius
  let S := sphere c R
  let χ := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val
  let Q := sourceCanonicalRoot hp hp1 φ.val
  let C : ℂ → ℂ := fun w => (Q w)⁻¹*χ w
  let T : ℕ → ℂ → ℂ := fun N w => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
    sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w
  have hgeom := ch.geometry φ.val hφ
  have hcircle : S ⊆ sourceCanonicalRootDomain hp hp1 φ.val :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ.val k c R hgeom.1 hgeom.2
  have hμne (m : ℤ) (w : ℂ) (hw : w ∈ S) :
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m ≠ w :=
    canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain hp hp1 .dirichlet
      φ.val φ.property m w (hcircle hw)
  have hχne (w : ℂ) (hw : w ∈ S) : χ w ≠ 0 := by
    intro hz
    obtain ⟨m,hm⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 .dirichlet φ.val w).mp
      ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 .dirichlet φ.val w).mp hz)
    exact hμne m w hw hm
  have hQne (w : ℂ) (hw : w ∈ S) : Q w ≠ 0 :=
    sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ.val w (hcircle hw)
  have hC (w : ℂ) (hw : w ∈ S) : AnalyticAt ℂ C w :=
    ((sourceCanonicalRoot_analyticOnNhd hp hp1 φ.val w (hcircle hw)).inv (hQne w hw)).mul
      (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w (mem_univ _))
  have hCcont : ContinuousOn C S := fun w hw => (hC w hw).continuousAt.continuousWithinAt
  let L := ‖c‖+R
  have hL : 0 ≤ L := by dsimp only [L,R]; linarith [norm_nonneg c,ch.spectralRadius_pos]
  have hS : S ⊆ {w | ‖w‖ ≤ L ∧ χ w ≠ 0} := by
    intro w hw
    have he : ‖w-c‖ = R := by simpa only [S,mem_sphere,dist_eq_norm] using hw
    have hb := norm_add_le (w-c) c
    rw [sub_add_cancel,he] at hb
    exact ⟨by dsimp only [L]; linarith,hχne w hw⟩
  have ht : TendstoUniformlyOn T (fun w => sourcePsiCandidate n (w,a)/χ w) atTop S :=
    (tendstoUniformlyOn_sourcePsiDirichletInterpolation hp hp1 n a φ L hL).mono hS
  obtain ⟨M,hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hCcont
  have hMpos : 0 < max 1 M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hu := tendstoUniformlyOn_bounded_const_mul ht (max 1 M) hMpos
    (fun w hw => (hM w hw).trans (le_max_right _ _))
  have hterm (m : ℤ) (w : ℂ) (hw : w ∈ S) :
      AnalyticAt ℂ (fun w => C w*sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) w := by
    have ht : AnalyticAt ℂ (fun w : ℂ => sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) w :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (hμne m w hw).symm)
    exact (hC w hw).mul ht
  have hcont (N : ℕ) : ContinuousOn (fun w => C w*T N w) S := by
    intro w hw
    have ht : AnalyticAt ℂ (fun w => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        C w*sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) w :=
      Finset.analyticAt_fun_sum _ (fun m _ => hterm m w hw)
    simpa only [T,Finset.mul_sum] using ht.continuousAt.continuousWithinAt
  have hi := hu.tendsto_circleIntegral_of_continuousOn ch.spectralRadius_pos.le
    (Filter.Eventually.of_forall hcont)
  have hlimit : (∮ w in C(c,R), C w*(sourcePsiCandidate n (w,a)/χ w)) =
      ∮ w in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (w,(a,φ.val)) := by
    apply circleIntegral.integral_congr ch.spectralRadius_pos.le
    intro w hw
    change (Q w)⁻¹*χ w*(sourcePsiCandidate n (w,a)/χ w) = sourcePsiCandidate n (w,a)/Q w
    field_simp [hχne w hw,hQne w hw]
  rw [hlimit] at hi
  have hfinite (N : ℕ) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,a)*
          sourceDirichletActionKernel hp hp1 m k ch φ.val) =
      (2*Real.pi : ℂ)⁻¹*(∮ w in C(c,R), C w*T N w) := by
    rw [show (∮ w in C(c,R), C w*T N w) =
        ∑ m ∈ Finset.Icc (-(N : ℤ)) N, ∮ w in C(c,R),
          C w*sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w from by
      simp only [T,Finset.mul_sum]
      exact circleIntegral.integral_fun_sum (fun m _ =>
        (show ContinuousOn (fun w => C w*sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) S
          from fun w hw => (hterm m w hw).continuousAt.continuousWithinAt).circleIntegrable ch.spectralRadius_pos.le),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    let d := deriv χ μ
    have hd : d ≠ 0 := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
      hp hp1 .dirichlet φ.val φ.property m
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    change sourcePsiCandidate n (μ,a)*
      (-(Real.pi : ℂ)⁻¹*(2*d)⁻¹*(∮ w in C(c,R), (Q w)⁻¹*χ w/(μ-w))) = _
    calc
      _ = (-((Real.pi : ℂ)⁻¹)*(2*d)⁻¹*sourcePsiCandidate n (μ,a))*
          (∮ w in C(c,R), (Q w)⁻¹*χ w/(μ-w)) := by ring
      _ = ∮ w in C(c,R),
          (-((Real.pi : ℂ)⁻¹)*(2*d)⁻¹*sourcePsiCandidate n (μ,a))*((Q w)⁻¹*χ w/(μ-w)) :=
        (circleIntegral.integral_const_mul _ _ c R).symm
      _ = (2*Real.pi : ℂ)⁻¹*(∮ w in C(c,R),
          C w*sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr ch.spectralRadius_pos.le
        intro w hw
        dsimp only
        change _ = (2*Real.pi : ℂ)⁻¹*((Q w)⁻¹*χ w*(sourcePsiCandidate n (μ,a)/d/(w-μ)))
        have hμw : μ-w ≠ 0 := sub_ne_zero.mpr (hμne m w hw)
        have hwμ : w-μ ≠ 0 := sub_ne_zero.mpr (hμne m w hw).symm
        field_simp [hd,hπ,hμw,hwμ,hQne w hw]
        ring
  have hi' := hi.const_mul ((2*Real.pi : ℂ)⁻¹)
  exact hi'.congr' (Filter.Eventually.of_forall (fun N => (hfinite N).symm))

end NLS.ZakharovShabat
