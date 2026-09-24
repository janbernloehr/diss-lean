import NLS.ZakharovShabat.SourceCriticalRootRatioHomotopyDetours
import NLS.ZakharovShabat.SourceCriticalRootRatioContinuousOpenPathHomotopy

/-!
# Endpoint detours under continuous gap-avoiding deformations

The full endpoint path keeps its short singular vertical connectors.
The crossing now needs only a continuous fixed-endpoint deformation
from the horizontal segment, with twice-smooth gap-avoiding slices.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At either signed height, a continuous family of smooth crossings
through the root domain transfers the exact-zero dogleg integral. -/
theorem sourceCriticalRootRatio_continuousHomotopyDetour_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w)
    CurveIntegrable ω (Path.segment l (l+(y:ℂ)*Complex.I)) →
    CurveIntegrable ω (Path.segment r (r+(y:ℂ)*Complex.I)) →
    CurveIntegrable ω (Path.segment (l+(y:ℂ)*Complex.I)
      (r+(y:ℂ)*Complex.I)) →
    (∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y, ω z) = 0 →
    ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      ∀ H : ((Path.segment (l+(y:ℂ)*Complex.I)
        (r+(y:ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
        ∀ hends : (∀ s : I, H (s,0) = l+(y:ℂ)*Complex.I ∧
          H (s,1) = r+(y:ℂ)*Complex.I),
        (∀ s : I, ContDiffOn ℝ 2
          (sourceHomotopyPath H hends s).extend (Icc 0 1)) →
        (∀ s u : I, H (s,u) ∈ sourceCanonicalRootDomain hp hp1 ψ) →
        CurveIntegrable ω (sourceUpperGapDetourPath hp hp1 ψ n y γ) ∧
          (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n y γ, ω z) = 0 := by
  dsimp only
  intro hleft hright hmid hzero γ H hends hsmooth havoid
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
  have hγsmooth : ContDiffOn ℝ 2 γ.extend (Icc 0 1) := by
    have h := hsmooth 1
    have heq : sourceHomotopyPath H hends 1 = γ := by
      apply Path.ext
      funext u
      change H (1,u) = γ u
      exact H.apply_one u
    simpa only [heq] using h
  have hγdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    have hz := havoid 1 u
    rw [H.apply_one] at hz
    exact hz
  have hγInt : CurveIntegrable ω γ :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ γ
      (hγsmooth.of_le (by norm_num)) hγdom
  have hcross :=
    sourceCriticalRootRatio_openPathIntegral_eq_of_continuous_smooth_homotopy
      hp hp1 ψ hreal H hends hsmooth havoid
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
      rw [hcross]
    exact heq.trans hzero

/-- A continuous deformation with smooth gap-avoiding slices suffices
for exact vanishing of sufficiently short upper endpoint detours. -/
theorem exists_sourceCriticalRootRatio_upperContinuousHomotopyDetours_integrable_and_zero
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
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w)
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
        ∀ H : ((Path.segment (l+(y:ℂ)*Complex.I)
          (r+(y:ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
          ∀ hends : (∀ s : I, H (s,0) = l+(y:ℂ)*Complex.I ∧
            H (s,1) = r+(y:ℂ)*Complex.I),
            (∀ s : I, ContDiffOn ℝ 2
              (sourceHomotopyPath H hends s).extend (Icc 0 1)) →
            (∀ s u : I, H (s,u) ∈ sourceCanonicalRootDomain hp hp1 ψ) →
            CurveIntegrable ω (sourceUpperGapDetourPath hp hp1 ψ n y γ) ∧
              (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n y γ, ω z) = 0 := by
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
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro y hy γ H hends hsmooth havoid
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
  exact sourceCriticalRootRatio_continuousHomotopyDetour_integrable_and_zero
    hp hp1 ψ hreal n y hleft hright hmid (hzero y hy₂).2
    γ H hends hsmooth havoid

/-- The same continuous-homotopy result for sufficiently shallow
lower endpoint detours. -/
theorem exists_sourceCriticalRootRatio_lowerContinuousHomotopyDetours_integrable_and_zero
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
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w)
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ γ : Path (l+((-y:ℝ):ℂ)*Complex.I)
        (r+((-y:ℝ):ℂ)*Complex.I),
        ∀ H : ((Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
          (r+((-y:ℝ):ℂ)*Complex.I) : C(I,ℂ))).Homotopy γ,
          ∀ hends : (∀ s : I, H (s,0) = l+((-y:ℝ):ℂ)*Complex.I ∧
            H (s,1) = r+((-y:ℝ):ℂ)*Complex.I),
            (∀ s : I, ContDiffOn ℝ 2
              (sourceHomotopyPath H hends s).extend (Icc 0 1)) →
            (∀ s u : I, H (s,u) ∈ sourceCanonicalRootDomain hp hp1 ψ) →
            CurveIntegrable ω (sourceLowerGapDetourPath hp hp1 ψ n y γ) ∧
              (∫ᶜ z in sourceLowerGapDetourPath hp hp1 ψ n y γ, ω z) = 0 := by
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
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro y hy γ H hends hsmooth havoid
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
  change CurveIntegrable ω
    (sourceUpperGapDetourPath hp hp1 ψ n (-y) γ) ∧
    (∫ᶜ z in sourceUpperGapDetourPath hp hp1 ψ n (-y) γ, ω z) = 0
  exact sourceCriticalRootRatio_continuousHomotopyDetour_integrable_and_zero
    hp hp1 ψ hreal n (-y) hleft hright hmid (hzero y hy₂).2
    γ H hends hsmooth havoid

end NLS.ZakharovShabat
