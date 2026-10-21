import NLS.ZakharovShabat.SourcePeriodicLabelDiscontinuity
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginal

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a zero, continuity of the square forces continuity of a complex function,
even when its nonzero values use a discontinuous choice of square root. -/
theorem continuousAt_of_square_at_zero {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (x : X) (h : ContinuousAt (fun y => (f y)^2) x) (hz : f x = 0) :
    ContinuousAt f x := by
  have hn : ContinuousAt (fun y => ‖f y‖) x := by
    have hs := h.norm.sqrt
    simpa only [norm_pow,Real.sqrt_sq (norm_nonneg _)] using hs
  change Tendsto f (𝓝 x) (𝓝 (f x))
  rw [hz,tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hz,norm_zero] using hn.tendsto

/-- A continuous gap and midpoint would make the left endpoint continuous. -/
theorem continuousAt_sourcePeriodicLeft_of_midpoint_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ)
    (hm : ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)
    (hg : ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) :
    ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
  have he : (fun ψ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n/2) =
      (fun ψ : CoeffPair p =>
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) := by
    funext ψ
    unfold canonicalPeriodicMidpoint canonicalPeriodicGap
    ring
  rw [← he]
  exact hm.sub (hg.div_const 2)

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The literal central gap and the original eta phase modulo 2*pi both have
discontinuities within the original open-gap domain, arbitrarily close to zero. -/
theorem exists_original_gap_eta_phase_discontinuity
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    let G := fun ψ : CoeffPair p =>
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
    let E := fun ψ : CoeffPair p => Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 0 s ψ)
    let U := {ψ : CoeffPair p | ψ ∈ W ∧ G ψ ≠ 0}
    ∃ r : ℝ, 0 < r ∧ sourceConstantPotential (p := p) (r : ℂ) (-r) ∈ W ∩ V ∧
      G (sourceConstantPotential (p := p) (r : ℂ) (-r)) ≠ 0 ∧
      ¬ContinuousWithinAt G U (sourceConstantPotential (p := p) (r : ℂ) (-r)) ∧
      ¬ContinuousWithinAt E U (sourceConstantPotential (p := p) (r : ℂ) (-r)) := by
  dsimp only
  let G := fun ψ : CoeffPair p =>
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
  let E := fun ψ : CoeffPair p => Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 0 s ψ)
  let U := {ψ : CoeffPair p | ψ ∈ W ∧ G ψ ≠ 0}
  let D := H.original_theta_common_domain
  have hzero : (0 : CoeffPair p) ∈ W := D.real_subset (by simp [realTypeSourceLocus])
  obtain ⟨r,hr,hrWV,hL,_⟩ := exists_sourcePeriodicLabels_not_continuousAt
    hp hp1 (W ∩ V) (inter_mem (D.source_open.mem_nhds hzero) hV)
  let φ := sourceConstantPotential (p := p) (r : ℂ) (-r)
  have hm := (D.symmetric_analytic φ hrWV.1 0).1.continuousAt
  have hsq : ContinuousAt (fun ψ => (G ψ)^2) φ :=
    (D.symmetric_analytic φ hrWV.1 0).2.continuousAt
  have hg : ¬ContinuousAt G φ := fun hc =>
    hL (continuousAt_sourcePeriodicLeft_of_midpoint_gap hp hp1 φ 0 hm hc)
  have hgap : G φ ≠ 0 := fun hz => hg (continuousAt_of_square_at_zero G φ hsq hz)
  have hφU : φ ∈ U := ⟨hrWV.1,hgap⟩
  have hU : U ∈ 𝓝 φ := (D.open_gap 0).mem_nhds hφU
  refine ⟨r,hr,hrWV,hgap,fun hc => hg (hc.continuousAt hU),?_⟩
  intro hc
  have he : ContinuousAt E φ := hc.continuousAt hU
  have hz := (H.gapWeightedEta_original_analytic 0 1 φ hrWV.1).continuousAt
  have hquot : ContinuousAt (fun ψ => sourceGapWeightedEtaCoordinate hp hp1 0 s 1 ψ / E ψ) φ :=
    hz.div he (Complex.exp_ne_zero _)
  apply hg
  apply hquot.congr_of_eventuallyEq
  filter_upwards [hU] with ψ hψ
  have hvalue := H.gapWeightedEta_original_plus ψ hψ.1 0 hψ.2
  change G ψ = sourceGapWeightedEtaCoordinate hp hp1 0 s 1 ψ / E ψ
  rw [hvalue]
  exact (mul_div_cancel_right₀ (G ψ) (Complex.exp_ne_zero _)).symm

/-- Neither the actual gap nor the original eta phase modulo 2*pi is continuous
on the full original central open-gap domain. -/
theorem original_gap_eta_phase_not_continuousOn
    (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    let G := fun ψ : CoeffPair p =>
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
    let E := fun ψ : CoeffPair p => Complex.exp (Complex.I*sourceAngularOriginalEta hp hp1 0 s ψ)
    let U := {ψ : CoeffPair p | ψ ∈ W ∧ G ψ ≠ 0}
    ¬ContinuousOn G U ∧ ¬ContinuousOn E U := by
  obtain ⟨r,_,hrW,hgap,hG,hE⟩ := H.exists_original_gap_eta_phase_discontinuity univ univ_mem
  exact ⟨fun hc => hG (hc _ ⟨hrW.1,hgap⟩),fun hc => hE (hc _ ⟨hrW.1,hgap⟩)⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
