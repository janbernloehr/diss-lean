import NLS.ZakharovShabat.L2WeightedActionGradient
import NLS.ZakharovShabat.SourceHigherActionCotangentSymmetries
import NLS.ZakharovShabat.SourceLemma10ContourGeometry

/-! # Literal level-zero contour gradients under Lemma 10's symmetries

One original isolating circle works for every integer printed level. The
central circle encloses zero and the noncentral discs exclude it. In both
cases the circle itself avoids the pole, giving an actual analytic local
functional and its full continuous physical gradient, even at level zero.
This does not identify a globally patched Laurent action or assert the
remaining spatial recurrences.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem exists_sourceLaurentReflection_physical_gradients :
    ∃ W U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧
      ∀ φ ∈ U, SourcePeriodicReflection (by simp) (by norm_num) φ → ∀ n : ℤ,
        ∃ C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) φ n,
          (0:ℂ) ∉ sphere (C.center:ℂ) C.radius ∧
          (n = 0 → (0:ℂ) ∈ ball (C.center:ℂ) C.radius) ∧
          (n ≠ 0 → (0:ℂ) ∉ closedBall (C.center:ℂ) C.radius) ∧
          ∀ k : ℤ,
            AnalyticAt ℂ (fun ψ => sourceLaurentPrimitiveCircle (by simp) (by norm_num)
              W 0 k ψ (C.center:ℂ) C.radius) φ ∧
            SourcePhysicalGradientRepresents
              (fderiv ℂ (fun ψ => sourceLaurentPrimitiveCircle (by simp) (by norm_num)
                W 0 k ψ (C.center:ℂ) C.radius) φ)
              (sourceWeightedPhysicalGradientCurve φ (fun z => z^(k-1)) (C.center:ℂ) C.radius) := by
  obtain ⟨V,hV,_,hrV,H⟩ := sourceSection11Contours (p := 2) (by simp) (by norm_num)
  obtain ⟨W,A,_,D⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  refine ⟨W,V ∩ A,hV.inter D.source_open,fun φ hφ => ⟨hrV hφ,D.real_subset hφ⟩,?_⟩
  intro φ hφ hs n
  obtain ⟨B,hB,_,hφB,_,E,c,hE,F,_⟩ := H.neighborhoods φ hφ.1
  let C := F.periodCircle hE φ hφB n
  have hc := C.sphere_subset_rootDomain
  have hz := C.zero_not_mem_sphere_of_reflection hs
  have hrootO : IsOpen (sourceCanonicalRootJointDomain (by simp) (by norm_num) (B ∩ A)) := by
    have he : sourceCanonicalRootJointDomain (by simp) (by norm_num) (B ∩ A) =
        sourceCanonicalRootJointDomain (by simp) (by norm_num) A ∩ Prod.snd ⁻¹' B := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2,ht.2⟩,ht.1.1⟩,fun ht => ⟨⟨ht.2,ht.1.1⟩,ht.1.2⟩⟩
    rw [he]
    exact D.root_domain_open.inter (hB.preimage continuous_snd)
  refine ⟨C,hz,?_,fun hn => C.zero_not_mem_noncentral_disc_of_reflection hs hn,?_⟩
  · intro hn
    subst n
    exact C.zero_mem_central_ball_of_reflection hs
  · intro k
    have ha := sourceLaurentPrimitiveCircle_analyticOnNhd (by simp) (by norm_num) W (B ∩ A) 0 k
      (hB.inter D.source_open) hrootO
      ((D.analytic 0).mono (fun t ht => ⟨ht.1.2,ht.2⟩)) (C.center:ℂ) C.radius C.radius_pos.le
      (fun ψ hψ => (F.periodCircle hE ψ hψ.1 n).sphere_subset_rootDomain) hz
    refine ⟨ha φ ⟨hφB,hφ.2⟩,?_⟩
    intro h
    have hw : ContinuousOn (fun z : ℂ => z^(k-1)) (sphere (C.center:ℂ) C.radius) := by
      intro z hzc
      have haz : AnalyticAt ℂ (fun z : ℂ => z^(k-1)) z :=
        analyticAt_id.zpow (by intro he; exact hz (he ▸ hzc))
      exact haz.continuousAt.continuousWithinAt
    rw [← sourcePhysicalL2_gradient_pairing h,← l2GradientPairing_apply,
      sourceWeightedPhysicalGradientCurve_pairing φ h (fun z => z^(k-1))
        (C.center:ℂ) C.radius C.radius_pos.le hw hc]
    exact D.fderiv_laurentPrimitiveCircle 0 k φ hφ.2 (C.center:ℂ) C.radius C.radius_pos.le hc hz h

end NLS.ZakharovShabat
