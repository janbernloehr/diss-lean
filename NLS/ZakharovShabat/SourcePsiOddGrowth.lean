import NLS.ZakharovShabat.Section7PsiPeriodUniqueness

/-! The actual odd frequency numerator retains entire analyticity,
reality on the real axis, and sub-sine growth. A vanishing real gap
period supplies a zero in that gap, including collapsed gaps. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceOddPsiCandidate (n : ℤ) (t : ℂ × Coeff p) : ℂ :=
  sourcePsiCandidate n t-sourcePsiCandidate n (-t.1,t.2)

theorem analyticOnNhd_sourceOddPsiCandidate (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceOddPsiCandidate (p := p) n) univ := by
  intro t _
  exact (analyticOnNhd_sourcePsiCandidate hp hp1 n t (mem_univ _)).sub
    ((analyticOnNhd_sourcePsiCandidate hp hp1 n (-t.1,t.2) (mem_univ _)).comp
      (f := fun u : ℂ × Coeff p => (-u.1,u.2)) (analyticAt_fst.neg.prod analyticAt_snd))

theorem sourceOddPsiCandidate_real (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (ha : ∀ k : ℤ, (displacedRoots a k).im = 0) (x : ℝ) :
    (sourceOddPsiCandidate n ((x:ℂ),a)).im = 0 := by
  have hr (y : ℝ) : (sourcePsiCandidate n ((y:ℂ),a)).im = 0 := by
    have he := sourcePsiCandidate_conj_of_real_roots hp hp1 n a ha (y:ℂ)
    rw [Complex.conj_ofReal] at he
    exact Complex.conj_eq_iff_im.mp he.symm
  simp only [sourceOddPsiCandidate,Complex.sub_im,← Complex.ofReal_neg,hr,sub_self]

theorem sourceOddPsiCandidate_sub_sine_growth (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖sourceOddPsiCandidate n (z,a)/(-2*sin z)‖ ≤ ε := by
  obtain ⟨K,hK⟩ := section7_psi_sub_sine_growth hp hp1 n a (ε/2) (by positivity)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hnz : -z ∈ sphere (0:ℂ) (centralCircleRadius k) := by
    simpa only [mem_sphere,dist_zero_right,norm_neg] using hz
  have hneg : ‖sourcePsiCandidate n (-z,a)/(-2*sin z)‖ ≤ ε/2 := by
    simpa only [norm_div,norm_mul,sin_neg,norm_neg] using hK k hk (-z) hnz
  rw [sourceOddPsiCandidate,sub_div]
  exact (norm_sub_le _ _).trans (by linarith [hK k hk z hz])

theorem exists_sourceOddPsiCandidate_zero_in_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : Coeff p)
    (ha : ∀ k : ℤ, (displacedRoots a k).im = 0) (m : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 φ m)
    (hperiod : (∮ z in C((D.center:ℂ),D.radius),
      sourceOddPsiCandidate n (z,a)/sourceCanonicalRoot hp hp1 φ z) = 0) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 φ m, sourceOddPsiCandidate n (z,a) = 0 := by
  have hF : AnalyticOnNhd ℂ (fun z => sourceOddPsiCandidate n (z,a)) univ := by
    intro z _
    exact (analyticOnNhd_sourceOddPsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 φ hφ m with hclosed | hopen
  · have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 φ m
    exact ⟨_,hmid,sourceEntireNumerator_zero_at_collapsedGap hp hp1 φ hφ m _ hF
      hclosed (D.center:ℂ) D.radius D.radius_pos (D.gap hmid)
      D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain hperiod⟩
  · obtain ⟨z,hz,hzero⟩ := exists_sourceEntireNumerator_zero_on_openGap hp hp1 φ hφ m _ hF
      (sourceOddPsiCandidate_real hp hp1 n a ha) hopen D.center D.radius D.radius_pos
      D.gap D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain hperiod
    exact ⟨z,sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 φ m hz,hzero⟩

end NLS.ZakharovShabat
