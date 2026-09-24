import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointDetours
import NLS.ZakharovShabat.SourceCriticalRootRatioOpenPathHomotopy

/-!
# Endpoint detours through the gap complement

The crossing of a short singular endpoint dogleg may leave its
half-plane, provided a smooth fixed-endpoint homotopy through the
complement of all gap segments deforms the horizontal crossing to it.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact-zero endpoint-dogleg calculation transfers to any
smooth crossing homotopic to its horizontal segment through the
canonical-root domain. The height may have either sign. -/
theorem sourceCriticalRootRatio_homotopyDetour_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (y : ℝ)
    (hleft : CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w))
      (Path.segment
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
          (y:ℂ)*Complex.I)))
    (hright : CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w))
      (Path.segment
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
          (y:ℂ)*Complex.I)))
    (hmid : CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w))
      (Path.segment
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
          (y:ℂ)*Complex.I)
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n +
          (y:ℂ)*Complex.I)))
    (hzero : (∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) = 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
      ∀ H : ((Path.segment (l+(y:ℂ)*Complex.I)
        (r+(y:ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
        (∀ s : I, H (s,0) = l+(y:ℂ)*Complex.I ∧
          H (s,1) = r+(y:ℂ)*Complex.I) →
        range H ⊆ sourceCanonicalRootDomain hp hp1 ψ →
        ContDiffOn ℝ 2
          (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
          (Icc 0 1) →
        CurveIntegrable
          (NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w))
          (sourceUpperGapDetourPath hp hp1 ψ n y γ) ∧
        (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n y γ,
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) = 0 := by
  dsimp only
  intro γ hγ H hends havoid hsmooth
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
  have hγdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    have hz : H (1,u) ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      havoid ⟨(1,u),rfl⟩
    rw [H.apply_one] at hz
    exact hz
  have hγInt : CurveIntegrable ω γ :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ γ
      (hγ.of_le (by norm_num)) hγdom
  have hcross := sourceCriticalRootRatio_openPathIntegral_eq_of_homotopy_range
    hp hp1 ψ H hends havoid hsmooth
  constructor
  · change CurveIntegrable ω
      (((Path.segment l (l+(y:ℂ)*Complex.I)).trans γ).trans
        (Path.segment r (r+(y:ℂ)*Complex.I)).symm)
    exact (hleft.trans hγInt).trans hright.symm
  · have heq :
        (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n y γ, ω z) =
        ∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y, ω z := by
      change (∫ᶜ z in ((Path.segment l (l+(y:ℂ)*Complex.I)).trans γ).trans
        (Path.segment r (r+(y:ℂ)*Complex.I)).symm, ω z) = _
      rw [curveIntegral_trans (hleft.trans hγInt) hright.symm,
        curveIntegral_trans hleft hγInt, curveIntegral_symm]
      change _ = (∫ᶜ z in
        ((Path.segment l (l+(y:ℂ)*Complex.I)).trans
          (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))).trans
            (Path.segment r (r+(y:ℂ)*Complex.I)).symm, ω z)
      rw [curveIntegral_trans (hleft.trans hmid) hright.symm,
        curveIntegral_trans hleft hmid, curveIntegral_symm]
      rw [← hcross]
    exact heq.trans hzero

/-- At every sufficiently small positive height, a smooth crossing
homotopic to the horizontal segment through the root domain gives an
integrable, zero-integral endpoint path. Its image need not stay in
the upper half-plane. -/
theorem exists_sourceCriticalRootRatio_upperHomotopyDetours_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
        ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
        ∀ H : ((Path.segment (l+(y:ℂ)*Complex.I)
          (r+(y:ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
          (∀ s : I, H (s,0) = l+(y:ℂ)*Complex.I ∧
            H (s,1) = r+(y:ℂ)*Complex.I) →
          range H ⊆ sourceCanonicalRootDomain hp hp1 ψ →
          ContDiffOn ℝ 2
            (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
            (Icc 0 1) →
          CurveIntegrable
            (NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w))
            (sourceUpperGapDetourPath hp hp1 ψ n y γ) ∧
          (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n y γ,
            NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w) z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
  obtain ⟨ε₁,hε₁,hvertical⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hzero⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_integrable_and_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy γ hγ H hends havoid hsmooth
  have hy₁ : y ∈ Ioo (0:ℝ) ε₁ := ⟨hy.1,hy.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ := ⟨hy.1,hy.2.trans_le (min_le_right ε₁ ε₂)⟩
  have hleft : CurveIntegrable ω (Path.segment l (l+(y:ℂ)*Complex.I)) := by
    have h := hvertical (-1) (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hright : CurveIntegrable ω (Path.segment r (r+(y:ℂ)*Complex.I)) := by
    have h := hvertical 1 (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hmid : CurveIntegrable ω
      (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) :=
    sourceCriticalRootRatio_horizontalSegment_curveIntegrable
      hp hp1 ψ hreal n y (ne_of_gt hy.1)
  exact sourceCriticalRootRatio_homotopyDetour_integrable_and_zero
    hp hp1 ψ n y hleft hright hmid (hzero y hy₂).2
    γ hγ H hends havoid hsmooth

/-- The corresponding result holds for crossings based below the
real axis, even when their homotopic deformation subsequently leaves
the lower half-plane. -/
theorem exists_sourceCriticalRootRatio_lowerHomotopyDetours_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ γ : Path (l+((-y:ℝ):ℂ)*Complex.I)
        (r+((-y:ℝ):ℂ)*Complex.I),
        ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
        ∀ H : ((Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
          (r+((-y:ℝ):ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
          (∀ s : I, H (s,0) = l+((-y:ℝ):ℂ)*Complex.I ∧
            H (s,1) = r+((-y:ℝ):ℂ)*Complex.I) →
          range H ⊆ sourceCanonicalRootDomain hp hp1 ψ →
          ContDiffOn ℝ 2
            (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
            (Icc 0 1) →
          CurveIntegrable
            (NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w))
            (sourceLowerGapDetourPath hp hp1 ψ n y γ) ∧
          (∫ᶜ z in sourceLowerGapDetourPath hp hp1 ψ n y γ,
            NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w) z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
  obtain ⟨ε₁,hε₁,hvertical⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hzero⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_integrable_and_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy γ hγ H hends havoid hsmooth
  have hy₁ : y ∈ Ioo (0:ℝ) ε₁ := ⟨hy.1,hy.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ := ⟨hy.1,hy.2.trans_le (min_le_right ε₁ ε₂)⟩
  have hleft : CurveIntegrable ω
      (Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical (-1) (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hright : CurveIntegrable ω
      (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical 1 (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hmid : CurveIntegrable ω
      (Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
        (r+((-y:ℝ):ℂ)*Complex.I)) :=
    sourceCriticalRootRatio_horizontalSegment_curveIntegrable
      hp hp1 ψ hreal n (-y) (neg_ne_zero.2 (ne_of_gt hy.1))
  change CurveIntegrable ω (sourceUpperGapDetourPath hp hp1 ψ n (-y) γ) ∧
    (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n (-y) γ, ω z) = 0
  exact sourceCriticalRootRatio_homotopyDetour_integrable_and_zero
    hp hp1 ψ n (-y) hleft hright hmid (hzero y hy₂).2
    γ hγ H hends havoid hsmooth

end NLS.ZakharovShabat
