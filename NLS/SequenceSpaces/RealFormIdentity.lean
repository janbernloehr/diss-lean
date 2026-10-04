import NLS.SequenceSpaces.RealImag
import NLS.SequenceSpaces.RealCoeff
import NLS.ComplexAnalysis.RealFormIdentity
import NLS.ComplexAnalysis.ConvexHolomorphicIdentity

/-! # Holomorphic uniqueness from real coefficient pairs

Real and imaginary projections are contractions in the full sequence
norm. Agreement on the real pairs therefore determines Banach-valued
holomorphic functions on an open convex complex domain.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complex sequences with real coordinates. -/
def realLocus (p : ℝ≥0∞) : Set (Coeff p) := {a | ∀ n, (a n).im = 0}

/-- The rectangular real form of the complex Birkhoff coordinate space. -/
def realPairLocus (p : ℝ≥0∞) : Set (Coeff p × Coeff p) := realLocus p ×ˢ realLocus p

theorem norm_realPart_le (a : Coeff p) : ‖realPart a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
  intro n
  simpa only [realPart_apply,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_re_le_norm (a n)

theorem norm_imagPart_le (a : Coeff p) : ‖imagPart a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
  intro n
  simpa only [imagPart_apply,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_im_le_norm (a n)

/-- Real coordinate pairs are exactly the included real sequence pairs. -/
theorem mem_realPairLocus_iff (z : Coeff p × Coeff p) : z ∈ realPairLocus p ↔
    ∃ x : RealCoeff p × RealCoeff p,
      ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) x = z := by
  constructor
  · intro hz
    exact ⟨(reCLM p z.1,reCLM p z.2),Prod.ext
      (RealCoeff.complexCLM_reCLM p z.1 hz.1) (RealCoeff.complexCLM_reCLM p z.2 hz.2)⟩
  · rintro ⟨x,rfl⟩
    constructor <;> intro n <;> simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Agreement on real pairs near a real point gives a complex germ equality. -/
theorem eventuallyEq_of_realPair_agreement
    (f g : (Coeff p × Coeff p) → F) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (c : Coeff p × Coeff p) (hc : c ∈ U) (hcr : c ∈ realPairLocus p)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ z ∈ U, z ∈ realPairLocus p → f z = g z) : f =ᶠ[𝓝 c] g := by
  let re : (Coeff p × Coeff p) → (Coeff p × Coeff p) := fun z => (realPart z.1,realPart z.2)
  let im : (Coeff p × Coeff p) → (Coeff p × Coeff p) := fun z => (imagPart z.1,imagPart z.2)
  have hz := ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
    (realPairLocus p) c hcr (by
      intro x y hx hy
      constructor <;> intro n
      · change (x.1 n+y.1 n).im = 0
        simp [hx.1 n,hy.1 n]
      · change (x.2 n+y.2 n).im = 0
        simp [hx.2 n,hy.2 n]) (by
      intro t x hx
      constructor <;> intro n
      · change ((t:ℂ)*x.1 n).im = 0
        simp [hx.1 n]
      · change ((t:ℂ)*x.2 n).im = 0
        simp [hx.2 n]) re im
    (fun z => ⟨realPart_im_eq_zero z.1,realPart_im_eq_zero z.2⟩)
    (fun z => ⟨imagPart_im_eq_zero z.1,imagPart_im_eq_zero z.2⟩)
    (fun z => Prod.ext (realPart_add_I_imagPart z.1).symm (realPart_add_I_imagPart z.2).symm)
    (fun z => by exact max_le_max (norm_realPart_le z.1) (norm_realPart_le z.2))
    (fun z => by exact max_le_max (norm_imagPart_le z.1) (norm_imagPart_le z.2))
    U hU hc (f-g) (hf.sub hg) (fun z hz hr => sub_eq_zero.mpr (he z hz hr))
  exact hz.mono (fun z hz => sub_eq_zero.mp hz)

/-- Real-pair agreement determines the function throughout an open convex domain. -/
theorem eqOn_of_realPair_agreement
    (f g : (Coeff p × Coeff p) → F) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hconv : Convex ℝ U) (c : Coeff p × Coeff p)
    (hc : c ∈ U) (hcr : c ∈ realPairLocus p)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ z ∈ U, z ∈ realPairLocus p → f z = g z) : EqOn f g U :=
  ComplexAnalysis.DifferentiableOn.eqOn_of_convex_of_eventuallyEq f g U hU hconv hf hg c hc
    (eventuallyEq_of_realPair_agreement f g U hU c hc hcr hf hg he)

end NLS.Coeff
