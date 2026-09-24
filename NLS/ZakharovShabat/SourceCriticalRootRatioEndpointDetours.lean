import NLS.ZakharovShabat.SourceCriticalRootRatioLowerEndpointDoglegHeight
import NLS.ZakharovShabat.SourceCriticalRootRatioArbitraryHalfPlanePathLimit

/-!
# Smooth detours between singular gap endpoints

The straight crossing of either endpoint dogleg can be replaced by
an arbitrary twice-smooth path in the same half-plane. Convex
holomorphic path independence preserves its integral; the singular
vertical endpoint segments stay fixed and integrable.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Attach the upper singular endpoint connectors to an arbitrary
crossing path with the same shifted endpoints. -/
def sourceUpperGapDetourPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I) → Path l r := by
  dsimp only
  intro γ
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  exact ((Path.segment l (l+(y:ℂ)*Complex.I)).trans γ).trans
    (Path.segment r (r+(y:ℂ)*Complex.I)).symm

/-- Any smooth upper-half-plane crossing, with the same short
vertical branch-point connectors, gives an integrable path of
exactly zero quotient integral. -/
theorem exists_sourceCriticalRootRatio_upperDetours_integrable_and_zero
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
        (∀ u : I, 0 < (γ u).im) →
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
  intro y hy γ hγ hupper
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
  have hγInt : CurveIntegrable ω γ :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ γ
      (hγ.of_le (by norm_num)) (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_gt (hupper u)))
  have hcross := sourceCriticalRootRatio_upperPathIntegral_eq_horizontal
    hp hp1 ψ hreal n y hy.1 γ hγ hupper
  have hstraight := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
    hp hp1 ψ n y
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
      rw [hcross, ← hstraight]
    exact heq.trans (hzero y hy₂).2

/-- Positive `y` is the depth of the detour below the real axis. -/
def sourceLowerGapDetourPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :=
  sourceUpperGapDetourPath hp hp1 ψ n (-y)

/-- Every smooth lower-half-plane crossing with the same short
vertical branch-point connectors is integrable and has zero integral. -/
theorem exists_sourceCriticalRootRatio_lowerDetours_integrable_and_zero
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
      ∀ γ : Path (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I),
        ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
        (∀ u : I, (γ u).im < 0) →
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
  intro y hy γ hγ hlower
  have hy₁ : y ∈ Ioo (0:ℝ) ε₁ := ⟨hy.1,hy.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ := ⟨hy.1,hy.2.trans_le (min_le_right ε₁ ε₂)⟩
  have hleft : CurveIntegrable ω (Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical (-1) (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hright : CurveIntegrable ω (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical 1 (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hmid : CurveIntegrable ω
      (Path.segment (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I)) :=
    sourceCriticalRootRatio_horizontalSegment_curveIntegrable
      hp hp1 ψ hreal n (-y) (neg_ne_zero.2 (ne_of_gt hy.1))
  have hγInt : CurveIntegrable ω γ :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ γ
      (hγ.of_le (by norm_num)) (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_lt (hlower u)))
  have hcross := sourceCriticalRootRatio_lowerPathIntegral_eq_horizontal
    hp hp1 ψ hreal n (-y) (neg_lt_zero.mpr hy.1) γ hγ hlower
  have hstraight := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
    hp hp1 ψ n (-y)
  constructor
  · change CurveIntegrable ω
      (((Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)).trans γ).trans
        (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)).symm)
    exact (hleft.trans hγInt).trans hright.symm
  · have heq :
        (∫ᶜ z in sourceLowerGapDetourPath hp hp1 ψ n y γ, ω z) =
        ∫ᶜ z in sourceLowerGapDoglegPath hp hp1 ψ n y, ω z := by
      change (∫ᶜ z in ((Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)).trans γ).trans
        (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)).symm, ω z) = _
      rw [curveIntegral_trans (hleft.trans hγInt) hright.symm,
        curveIntegral_trans hleft hγInt, curveIntegral_symm]
      change _ = (∫ᶜ z in
        ((Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)).trans
          (Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
            (r+((-y:ℝ):ℂ)*Complex.I))).trans
            (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)).symm, ω z)
      rw [curveIntegral_trans (hleft.trans hmid) hright.symm,
        curveIntegral_trans hleft hmid, curveIntegral_symm]
      rw [hcross, ← hstraight]
    exact heq.trans (hzero y hy₂).2

end NLS.ZakharovShabat
