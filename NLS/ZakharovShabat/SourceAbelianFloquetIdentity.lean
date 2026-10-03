import NLS.ComplexAnalysis.NormalizedLogarithmicPrimitive
import NLS.ZakharovShabat.SourceFloquetEndpointLimit
import NLS.ZakharovShabat.SourceAbelianLocalExtension

/-! # The normalized abelian integral is a logarithm of the Floquet multiplier

The endpoint limit fixes the exponential exactly, with the signed gap's
parity factor. The identity holds on both full half-planes and throughout
their continuation across the isolating cut disc, without a principal
logarithm restriction.
-/
noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any actual endpoint-normalized primitive has the prescribed exponential. -/
theorem sourceAbelian_exp_eq_of_normalized_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (U : Set ℂ)
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hdom : U ⊆ sourceCanonicalRootDomain hp hp1 φ)
    [NeBot (𝓝[U] (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n))]
    (F : ℂ → ℂ) (hF : ∀ z ∈ U, HasDerivAt F
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z)
    (hFl : Tendsto F (𝓝[U]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0)) :
    ∀ z ∈ U, exp (F z) = sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z := by
  have hMl := (sourceFloquetMultiplier_tendsto_at_periodicEndpoint hp hp1 φ hφ n
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (by simp)).mono_left (nhdsWithin_mono _ hdom)
  have h := multiplier_eq_exp_of_normalized_primitive _ F (sourceFloquetMultiplier hp hp1 φ) U _
    (sourceAbelianGapSign n) hU hconn hF
    (fun z hz => hasDerivAt_sourceFloquetMultiplier hp hp1 φ hφ z (hdom hz)) hFl hMl
  intro z hz
  rw [h z hz,← mul_assoc,← pow_two,sourceAbelianGapSign_sq,one_mul]

/-- The complete upper and lower primitives are logarithms of the same
signed multiplier, with their normalization constants already fixed. -/
theorem sourceAbelianHalfPlanePrimitive_exp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    ∀ z ∈ sourceAbelianHalfPlane upper,
      exp (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper z) =
        sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z := by
  have hl := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  let := nhdsWithin_sourceAbelianHalfPlane_neBot upper _ hl
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  exact sourceAbelian_exp_eq_of_normalized_primitive hp hp1 φ hφ n _
    (isOpen_sourceAbelianHalfPlane upper) (convex_sourceAbelianHalfPlane upper).isPreconnected
    (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ upper) _ hs.1 hs.2.1

namespace SourceAbelianDiscPrimitive
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
  {hφ : IsRealType (CoeffPair.toMax p φ)} {n : ℤ}

/-- The same logarithm identity on the full disc complement. -/
theorem exp_eq (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    ∀ z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n,
      exp (D.toFun z) = sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  have hl : l ∈ ball D.center D.radius := D.segment_subset (left_mem_segment ℝ _ _)
  let : NeBot (𝓝[ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n] l) :=
    mem_closure_iff_nhdsWithin_neBot.mp
      ((dense_complex_segment_complement l r).open_subset_closure_inter isOpen_ball hl)
  exact sourceAbelian_exp_eq_of_normalized_primitive hp hp1 φ hφ n _ D.isOpen_discComplement
    (isPathConnected_convex_complex_segment_complement_including_singleton _ l r isOpen_ball
      (convex_ball _ _) hl).isConnected.isPreconnected
    (sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n D.center D.radius D.avoids_other)
    D.toFun D.hasDerivAt D.left_limit

/-- Exact exponential of the joined primitive, including its real-axis values. -/
theorem extension_exp (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    exp (D.extension z) = sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z := by
  rcases hz with (hu | hl) | hd
  · rw [D.extension_eq_halfPlane true hu]
    exact sourceAbelianHalfPlanePrimitive_exp hp hp1 φ hφ n true z hu
  · rw [D.extension_eq_halfPlane false hl]
    exact sourceAbelianHalfPlanePrimitive_exp hp hp1 φ hφ n false z hl
  · rw [D.extension_eq_disc hd]
    exact D.exp_eq z hd

/-- The opposite exponential is the signed companion multiplier. -/
theorem extension_exp_neg (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    exp (-D.extension z) = sourceAbelianGapSign n*
      ((canonicalDiscriminant hp (periodOnePotential φ) z-sourceCanonicalRoot hp hp1 φ z)/2) := by
  apply mul_left_cancel₀ (exp_ne_zero (D.extension z))
  rw [← exp_add,add_neg_cancel,exp_zero,D.extension_exp z hz]
  have hc := sourceFloquetMultiplier_mul_companion hp hp1 φ z (D.extensionDomain_subset_rootDomain hz)
  calc
    (1 : ℂ) = sourceAbelianGapSign n^2 *
        (sourceFloquetMultiplier hp hp1 φ z *
          ((canonicalDiscriminant hp (periodOnePotential φ) z-sourceCanonicalRoot hp hp1 φ z)/2)) := by
      rw [hc,sourceAbelianGapSign_sq,mul_one]
    _ = _ := by ring

/-- Recover the discriminant from the actual normalized primitive. -/
theorem extension_cosh (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    cosh (D.extension z) = sourceAbelianGapSign n *
      canonicalDiscriminant hp (periodOnePotential φ) z / 2 := by
  rw [Complex.cosh,D.extension_exp z hz,D.extension_exp_neg z hz,sourceFloquetMultiplier]
  ring

/-- Recover the oriented canonical root, so the identity retains the
sheet information lost by the square identity alone. -/
theorem extension_sinh (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    sinh (D.extension z) = sourceAbelianGapSign n * sourceCanonicalRoot hp hp1 φ z / 2 := by
  rw [Complex.sinh,D.extension_exp z hz,D.extension_exp_neg z hz,sourceFloquetMultiplier]
  ring

/-- The real part is fixed globally by the multiplier modulus, with no
remaining logarithm branch ambiguity or index-dependent constant. -/
theorem extension_re_eq_log_norm_multiplier (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    (D.extension z).re = Real.log ‖sourceFloquetMultiplier hp hp1 φ z‖ := by
  have h := congrArg norm (D.extension_exp z hz)
  rw [Complex.norm_exp,norm_mul,norm_sourceAbelianGapSign,one_mul] at h
  rw [← h,Real.log_exp]

/-- Inside the principal imaginary strip, the branch is the principal logarithm. -/
theorem extension_eq_log (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain)
    (hlo : -Real.pi < (D.extension z).im) (hhi : (D.extension z).im ≤ Real.pi) :
    D.extension z = log (sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z) := by
  rw [← D.extension_exp z hz]
  exact (Complex.log_exp hlo hhi).symm

/-- Endpoint normalization selects the principal logarithm near either
endpoint, simultaneously for every approach in the joined domain. -/
theorem extension_eventually_eq_log_at_endpoint (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    D.extension =ᶠ[𝓝[D.extensionDomain] a]
      (fun z => log (sourceAbelianGapSign n*sourceFloquetMultiplier hp hp1 φ z)) := by
  have hi : Tendsto (fun z => (D.extension z).im) (𝓝[D.extensionDomain] a) (𝓝 0) := by
    simpa only [Function.comp_def,Complex.zero_im] using
      (continuous_im.tendsto (0 : ℂ)).comp (D.extension_endpoint_limit a ha)
  filter_upwards [self_mem_nhdsWithin,
    hi.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)] with z hz him
  exact D.extension_eq_log z hz him.1 him.2.le

end SourceAbelianDiscPrimitive
end NLS.ZakharovShabat
