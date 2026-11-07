import NLS.ZakharovShabat.SourceHigherActionOneNormalized
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleComplexAgreement

/-! The filled first higher action is computed on the SAME fixed
free-centered circles for ALL distant labels on ONE complex source
neighborhood. Both the actual indexed action and the prescribed
collapsed-gap value are retained. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_source_free_eighth_periodCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        ∃ D : SourceCriticalRootPeriodCircle hp hp1 ψ n,
          (D.center : ℂ) = (Real.pi:ℂ)*n ∧ D.radius = Real.pi/8 := by
  obtain ⟨N,ε,_,_,V₀,hV₀,_,hφV₀,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 φ hφ
  obtain ⟨Kg,Vg,hVg,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  refine ⟨max (N+1) Kg,V₀ ∩ Vg,hV₀.inter hVg,⟨hφV₀,hφVg⟩,?_⟩
  intro ψ hψ n hn
  have hnN : ¬n.natAbs ≤ N := by omega
  have hnG : Kg ≤ n.natAbs := (le_max_right _ _).trans hn
  have he : sourceIsolatingDisc hp hp1 φ N ε n =
      ball ((Real.pi*(n:ℝ):ℝ):ℂ) (Real.pi/4) := by
    simp only [sourceIsolatingDisc,if_neg hnN,refinedResonantDisk]
    push_cast
    rfl
  let E := hD.periodCircle ψ hψ.1 n (Real.pi*(n:ℝ)) (Real.pi/4) (by positivity) he
  let D : SourceCriticalRootPeriodCircle hp hp1 ψ n := {
    center := Real.pi*(n:ℝ)
    radius := Real.pi/8
    radius_pos := by positivity
    gap := by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using (hgeom ψ hψ.2 n hnG).1
    other := by
      intro m hm w hw
      rcases E.other m hm w hw with h | h
      · exact Or.inl (by change w.re < Real.pi*(n:ℝ)-Real.pi/4 at h; nlinarith [Real.pi_pos])
      · exact Or.inr (by change Real.pi*(n:ℝ)+Real.pi/4 < w.re at h; nlinarith [Real.pi_pos]) }
  exact ⟨D,by simp only [D,Complex.ofReal_mul,Complex.ofReal_intCast],rfl⟩

theorem exists_local_sourceHigherActionOneNormalized_uniform_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        sourceHigherActionOneNormalized hp hp1 n ψ =
          sourceHigherActionOneCircleQuotient hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8) ψ ∧
        sourceIndexedHigherAction hp hp1 n 1 ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
            sourceHigherActionOneCircleQuotient hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8) ψ := by
  obtain ⟨Kd,Vd,hVd,hφVd,hcircles⟩ := exists_local_source_free_eighth_periodCircles hp hp1 φ hφ
  obtain ⟨Kz,rz,hrz,hzero⟩ := exists_local_source_distantCriticalRootRatio_freeCircle_zero hp hp1 φ hφ
  obtain ⟨Kg,Vg,hVg,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  obtain ⟨W,hW,_,hrealW,hoffset⟩ := exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let V := (Vd ∩ ball φ rz) ∩ (Vg ∩ W)
  refine ⟨max Kd (max Kz Kg),V,(hVd.inter isOpen_ball).inter (hVg.inter hW),
    ⟨⟨hφVd,mem_ball_self hrz⟩,hφVg,hrealW hφ⟩,?_⟩
  intro ψ hψ n hn
  have hd : Kd ≤ n.natAbs := (le_max_left _ _).trans hn
  have hz : Kz ≤ n.natAbs := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hg : Kg ≤ n.natAbs := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  obtain ⟨D,hDc,hDr⟩ := hcircles ψ hψ.1.1 n hd
  obtain ⟨hseg,_,hE,_,_⟩ := hgeom ψ hψ.2.1 n hg
  have hf : sourceIndexedHigherAction hp hp1 n 1 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
        sourceHigherActionOneCircleQuotient hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8) ψ := by
    rw [sourceIndexedHigherAction_eq_circle D 1,hDc,hDr,
      sourceHigherActionCircle_one_eq_squaredGap_mul_kernel hp hp1 ψ n _ _ _ (by positivity)
        (by simpa only [hDc,hDr] using D.sphere_subset_rootDomain)
        (hzero ψ hψ.1.2 n hz) hE (hoffset ψ hψ.2.2 n).2,
      sourceHigherActionOneCircleQuotient_eq_kernel]
    ring
  refine ⟨?_,hf⟩
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · rw [sourceHigherActionOneNormalized,if_pos hgap]
    have hc : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n =
        sourceStandardRootMidpoint hp hp1 ψ n := by
      have h := (hoffset ψ hψ.2.2 n).2
      rw [hgap,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul] at h
      exact sub_eq_zero.mp h
    exact (sourceHigherActionOneCircleQuotient_collapsed hp hp1 ψ n _ _ (by positivity)
      hgap hc hseg hE).symm
  · rw [sourceHigherActionOneNormalized,if_neg hgap,hf]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hgap)

end NLS.ZakharovShabat
