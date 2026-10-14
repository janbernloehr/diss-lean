import NLS.ComplexAnalysis.PiecewiseC1Loop
import NLS.ZakharovShabat.SourceStandardRootLogPrimitive
import NLS.ZakharovShabat.SourceLemma10_1

/-!
# Inverse-root integrals on arbitrary piecewise C¹ contours

A single-valued logarithmic correction reduces the integral to the negative
midpoint winding integral. Primitive values telescope across all corners.
On distinct isolating disks the inverse root has a primitive, so the integral
vanishes. Thus winding one around the selected gap gives the negative
Kronecker delta, without a circle or homotopy hypothesis.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inverse-root integral equals the negative midpoint-pole integral on every gap-avoiding contour. -/
theorem sourceStandardRoot_inv_piecewiseIntegral_eq_neg_midpoint_pole
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (sourcePeriodicSegment hp hp1 ψ n)ᶜ) :
    Γ.integral (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      -Γ.integral (fun z =>
        (z-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)⁻¹) := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2
  let A := (sourcePeriodicSegment hp hp1 ψ n)ᶜ
  let f : ℂ → ℂ := fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹
  let q : ℂ → ℂ := fun w => (w-t)⁻¹
  have hnonzero (w : ℂ) (hw : w ∈ A) : w-t ≠ 0 := by
    intro he
    exact hw (sub_eq_zero.mp he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hf : ContinuousOn f A := fun w hw =>
    (sourceStandardRoot_inv_analyticAt hp hp1 ψ n w hw).continuousAt.continuousWithinAt
  have hq : ContinuousOn q A := fun w hw =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (hnonzero w hw)).continuousWithinAt
  have hprim (w : ℂ) (hw : w ∈ A) :
      HasDerivAt (standardRootLogCorrection t g) (f w+q w) w :=
    hasDerivAt_standardRootLogCorrection t g w
      (fun he => hnonzero w hw (sub_eq_zero.mpr he.symm))
      (sourceStandardRoot_radicand_mem_slitPlane hp hp1 ψ n w hw)
  have hzero := Γ.integral_eq_zero_of_primitive (fun w => f w+q w)
    (standardRootLogCorrection t g) A (hf.add hq) hprim hΓ
  rw [Γ.integral_add f q hf hq hΓ] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- The full winding formula includes repeated traversals, reversed orientation and collapsed gaps. -/
theorem normalized_sourceStandardRoot_inv_piecewiseIntegral_eq_neg_winding
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (sourcePeriodicSegment hp hp1 ψ n)ᶜ) :
    Γ.normalizedIntegral (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      -Γ.windingIntegral
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) := by
  simp only [PiecewiseC1Loop.windingIntegral,PiecewiseC1Loop.normalizedIntegral]
  rw [sourceStandardRoot_inv_piecewiseIntegral_eq_neg_midpoint_pole hp hp1 ψ n Γ hΓ]
  ring

/-- Off-diagonal inverse roots integrate to zero on every piecewise C¹ contour inside its assigned disk. -/
theorem SourceIsolatingNeighborhoods.standardRoot_piecewiseIntegral_off_index
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (m n : ℤ) (hmn : m ≠ n)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D m)) :
    Γ.integral (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) = 0 := by
  obtain ⟨a,r,_,hball⟩ := h.discs m
  apply Γ.integral_eq_zero_of_convex _ (D m)
    (hball ▸ isOpen_ball) (hball ▸ convex_ball _ _) ?_ hΓ
  intro z hz
  have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n :=
    fun hg => Set.disjoint_left.mp (h.disjoint m n hmn) hz (h.gap ψ hψ n hg)
  exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z hnot).differentiableAt.differentiableWithinAt

/-- Lemma 10.3's contour identity with conventional winding-one orientation around the selected gap. -/
theorem SourceIsolatingNeighborhoods.standardRoot_piecewiseIntegral_indexed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (m n : ℤ)
    (Γ : PiecewiseC1Loop) (hinside : Γ.Inside (D m))
    (havoid : Γ.Inside (sourcePeriodicSegment hp hp1 ψ m)ᶜ)
    (hwinding : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) = 1) :
    Γ.normalizedIntegral (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      if m = n then -1 else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [normalized_sourceStandardRoot_inv_piecewiseIntegral_eq_neg_winding hp hp1 ψ m Γ havoid,hwinding]
    simp
  · rw [if_neg hmn,PiecewiseC1Loop.normalizedIntegral,
      h.standardRoot_piecewiseIntegral_off_index ψ hψ m n hmn Γ hinside,mul_zero]

end NLS.ZakharovShabat
