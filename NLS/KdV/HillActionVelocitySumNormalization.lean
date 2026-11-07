import NLS.KdV.HillEnergyDirichletInterpolation
import NLS.KdV.HillPrescribedActionCircle
import NLS.ZakharovShabat.AuxiliaryGapSegmentPlacement

/-! Evaluation of the actual complete Hill spectral velocity sum.
Uniform filled Dirichlet interpolation on the prescribed action
circle gives its original normalized psi period, with negative sign
for the phase/action order of the native Gardner bracket. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem auxiliaryDirichlet_ne_of_rootDomain (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (w : ℂ) (hw : w ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q)) :
    auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) w ≠ 0 := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  intro hz
  obtain ⟨m,hm⟩ := (mem_range_hillMiuraDiracDirichlet_iff u.val w).mpr hz
  have hmem := canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType
    (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) (P.sourcePsi_real q hq hr) m
  exact hw m (hm ▸ hmem)

theorem tendsto_prescribed_action_velocity_sums (P : HillProductEquationPatch)
    (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
        (hillHminusCanonicalDirichlet m q,q)*P.prescribedActionDirichletVelocity k m q) j) atTop
        (𝓝 (-(if k=n then (1:ℂ) else 0))) := by
  let a : ℂ := P.centers ((k:ℕ):ℤ)
  let R := P.radii ((k:ℕ):ℤ)
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let Q := sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q)
  let C : ℂ → ℂ := fun w => w/Q w
  let T : ℕ → ℂ → ℂ := fun N w => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
    positiveScalarExtension (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) j
  let S := sphere a R
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((k:ℕ):ℤ)
    (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hR : 0 < R := P.radii_pos _
  have hcircle : S ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q) :=
    D.sphere_subset_rootDomain
  have hdir := P.source_subset_canonicalDirichlet hq
  have hC (w : ℂ) (hw : w ∈ S) : AnalyticAt ℂ C w :=
    analyticAt_id.div (sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num)
      (P.sourcePsi q) w (hcircle hw))
      (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) (P.sourcePsi q) w (hcircle hw))
  have hterm (j : ℤ) (w : ℂ) (hw : w ∈ S) : AnalyticAt ℂ (fun z => C z*
      positiveScalarExtension (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (z^2-c)) j) w := by
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change AnalyticAt ℂ (fun z => C z*positiveScalarExtension
        (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (z^2-c)) ((m:ℕ):ℤ)) w
      simp only [positiveScalarExtension_apply]
      exact (hC w hw).mul ((analyticOnNhd_hillHminusPsiDirichletInterpolationTerm n m q hdir (w^2-c)
        (mem_univ _)).comp (f := fun z : ℂ => z^2-c) ((analyticAt_id.pow 2).sub analyticAt_const))
    · have hz (z : ℂ) : positiveScalarExtension
          (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (z^2-c)) j = 0 :=
        positiveScalarExtension_zero_of_not_mem_range _ j hj
      simp only [hz,mul_zero]
      exact analyticAt_const
  have hcont (N : ℕ) : ContinuousOn (fun w => C w*T N w) S := by
    intro w hw
    have ha := Finset.analyticAt_fun_sum (Finset.Icc (-(N:ℤ)) N) (fun j _ => hterm j w hw)
    simpa only [T,Finset.mul_sum] using ha.continuousAt.continuousWithinAt
  have ht := P.tendstoUniformlyOn_Hill_Dirichlet_interpolation n q hq hr S (isCompact_sphere a R)
    (fun w hw => P.auxiliaryDirichlet_ne_of_rootDomain q hq hr w (hcircle hw))
  obtain ⟨M,hM⟩ := (isCompact_sphere a R).exists_bound_of_continuousOn
    (show ContinuousOn C S from fun w hw => (hC w hw).continuousAt.continuousWithinAt)
  have hMpos : 0 < max 1 M := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  have hu := tendstoUniformlyOn_bounded_const_mul (c := C) ht (max 1 M) hMpos
    (fun w hw => (hM w hw).trans (le_max_right _ _))
  have hi := hu.tendsto_circleIntegral_of_continuousOn hR.le (Eventually.of_forall hcont)
  have heach (j : ℤ) : positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
        (hillHminusCanonicalDirichlet m q,q)*P.prescribedActionDirichletVelocity k m q) j =
      -(Real.pi:ℂ)⁻¹*(∮ w in C(a,R), C w*positiveScalarExtension
        (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) j) := by
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
          (hillHminusCanonicalDirichlet m q,q)*P.prescribedActionDirichletVelocity k m q) ((m:ℕ):ℤ) =
        -(Real.pi:ℂ)⁻¹*(∮ w in C(a,R), C w*positiveScalarExtension
          (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) ((m:ℕ):ℤ))
      simp only [positiveScalarExtension_apply]
      have hint : (∮ w in C(a,R), C w*hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) =
          (hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)/
            deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q))*
              (∮ w in C(a,R), C w*hillHminusDirichletFilledQuotient m (w^2-c,q)) := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr hR.le
        intro w _
        dsimp only [hillHminusPsiDirichletInterpolationTerm]
        ring
      rw [hint]
      change hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        (-(Real.pi:ℂ)⁻¹*(deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q))⁻¹*
          (∮ w in C(a,R), C w*hillHminusDirichletFilledQuotient m (w^2-c,q))) = _
      simp only [div_eq_mul_inv]
      ring
    · have hz (w : ℂ) : positiveScalarExtension
          (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) j = 0 :=
        positiveScalarExtension_zero_of_not_mem_range _ j hj
      rw [positiveScalarExtension_zero_of_not_mem_range _ j hj]
      simp only [hz,mul_zero]
      simp [circleIntegral]
  have hfinite (N : ℕ) : (∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
        (hillHminusCanonicalDirichlet m q,q)*P.prescribedActionDirichletVelocity k m q) j) =
      -(Real.pi:ℂ)⁻¹*(∮ w in C(a,R), C w*T N w) := by
    rw [show (∮ w in C(a,R), C w*T N w) =
        ∑ j ∈ Finset.Icc (-(N:ℤ)) N, ∮ w in C(a,R), C w*positiveScalarExtension
          (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q (w^2-c)) j from by
      simp only [T,Finset.mul_sum]
      exact circleIntegral.integral_fun_sum (fun j _ =>
        (show ContinuousOn _ S from fun w hw => (hterm j w hw).continuousAt.continuousWithinAt).circleIntegrable hR.le),
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => heach j)
  let J := ∮ w in C(a,R), C w*hillHminusCanonicalPsi n (w^2-c,q)
  have hdouble : (∮ w in C(a,R), P.abelianFrequencyDifferential n (w,q)) = 2*J := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro w _
    change (2*w*hillHminusCanonicalPsi n (w^2-c,q))/Q w = 2*((w/Q w)*hillHminusCanonicalPsi n (w^2-c,q))
    ring
  have hp := P.abelianFrequencyDifferential_period n k q hq D
  change (2*(Real.pi:ℂ))⁻¹*(∮ w in C(a,R), P.abelianFrequencyDifferential n (w,q)) = (if k=n then (1:ℂ) else 0) at hp
  rw [hdouble] at hp
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (2*Real.pi:ℂ)⁻¹*(2*J)=(Real.pi:ℂ)⁻¹*J := by field_simp [hπ]
  rw [hs] at hp
  have hlim : -(Real.pi:ℂ)⁻¹*J = -(if k=n then (1:ℂ) else 0) := by linear_combination -hp
  have hi' := hi.const_mul (-(Real.pi:ℂ)⁻¹)
  change Tendsto (fun N : ℕ => -(Real.pi:ℂ)⁻¹*(∮ w in C(a,R), C w*T N w)) atTop
    (𝓝 (-(Real.pi:ℂ)⁻¹*J)) at hi'
  rw [hlim] at hi'
  exact hi'.congr' (Eventually.of_forall (fun N => (hfinite N).symm))

end NLS.KdV.HillProductEquationPatch
