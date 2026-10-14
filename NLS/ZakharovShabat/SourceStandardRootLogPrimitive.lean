import NLS.ZakharovShabat.SourceStandardRootContourBasic
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A global logarithmic correction for inverse standard roots

Off the closed gap, the inverse root differs from the negative midpoint
pole by a derivative of a single-valued logarithm. This proves contour
normalization without a supplied homotopy or a restriction to circles.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- The principal logarithm of the normalized root factor, with the sign fixing its period. -/
def standardRootLogCorrection (t g z : ℂ) : ℂ :=
  -Complex.log (1+Complex.sqrt (1-g/(4*(t-z)^2)))

/-- Its derivative is the inverse standard root plus the positive midpoint pole. -/
theorem hasDerivAt_standardRootLogCorrection (t g z : ℂ) (hz : t ≠ z)
    (hslit : 1-g/(4*(t-z)^2) ∈ Complex.slitPlane) :
    HasDerivAt (standardRootLogCorrection t g)
      ((normalizedStandardRoot t g z)⁻¹+(z-t)⁻¹) z := by
  let R : ℂ → ℂ := fun w => 1-g/(4*(t-w)^2)
  let S : ℂ → ℂ := fun w => Complex.sqrt (R w)
  have ha : t-z ≠ 0 := sub_ne_zero.mpr hz
  have hR : HasDerivAt R (-g/(2*(t-z)^3)) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_const z g).div (((hasDerivAt_const z t).sub (hasDerivAt_id z)).pow 2 |>.const_mul 4)
        (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))) using 1 <;> try rfl
    simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
    field_simp
    ring
  have hS : DifferentiableAt ℂ S z := by
    simpa only [Function.comp_def] using!
      (Complex.differentiableAt_sqrt (z := R z) hslit).comp z hR.differentiableAt
  have hsquare (w : ℂ) : (S w)^2 = R w := by
    simpa only [S,Complex.sqrt,Nat.cast_ofNat] using Complex.cpow_nat_inv_pow (R w) (by norm_num : (2 : ℕ) ≠ 0)
  have hSd : 2*S z*deriv S z = -g/(2*(t-z)^3) := by
    have hd := hS.hasDerivAt.pow 2
    have hd' : HasDerivAt R (2*S z*deriv S z) z := by
      have heq : S^2 = R := funext hsquare
      simpa only [heq,Nat.cast_ofNat,pow_one,show (2 : ℕ)-1=1 from rfl] using hd
    exact hd'.unique hR
  have hS0 : S z ≠ 0 := by
    intro hs
    have hx := hsquare z
    rw [hs,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hx
    exact Complex.slitPlane_ne_zero hslit hx.symm
  have hpos : 0 < (1+S z).re := by
    have hnonneg : 0 ≤ (S z).re := by
      dsimp [S]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      exact Real.sqrt_nonneg _
    simp only [Complex.add_re,Complex.one_re]
    linarith
  have hlogslit : 1+S z ∈ Complex.slitPlane := Or.inl hpos
  have hlog0 : 1+S z ≠ 0 := Complex.slitPlane_ne_zero hlogslit
  have hd := ((hS.hasDerivAt.const_add 1).clog hlogslit).neg
  apply hd.congr_deriv
  have hsq := hsquare z
  dsimp [R] at hsq
  symm
  change ((t-z)*S z)⁻¹+(z-t)⁻¹ = -(deriv S z/(1+S z))
  have hneg : z-t = -(t-z) := by ring
  rw [hneg]
  field_simp [ha,hS0,hlog0] at hSd hsq ⊢
  apply mul_left_cancel₀ (show (4 : ℂ)*(t-z)^2 ≠ 0 from
    mul_ne_zero (by norm_num) (pow_ne_zero _ ha))
  linear_combination hSd-hsq


open NLS.ComplexAnalysis
open scoped unitInterval ENNReal

/-- Every C¹ closed path avoiding the gap has the negative midpoint-pole integral. -/
theorem sourceStandardRoot_inv_curveIntegral_eq_neg_midpoint_pole
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : NLS.CoeffPair p) (n : ℤ) {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (havoid : ∀ u : I, γ u ∉ sourcePeriodicSegment hp hp1 ψ n) :
    (∫ᶜ z in γ, holomorphicOneForm (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      -(∫ᶜ z in γ, holomorphicOneForm (fun w =>
        (w-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)⁻¹) z) := by
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
  have hfω : ContinuousOn (holomorphicOneForm f) A := hf.smul continuousOn_const
  have hqω : ContinuousOn (holomorphicOneForm q) A := hq.smul continuousOn_const
  have hfint := hfω.curveIntegrable_of_contDiffOn hγ havoid
  have hqint := hqω.curveIntegrable_of_contDiffOn hγ havoid
  have hprim (w : ℂ) (hw : w ∈ A) :
      HasDerivAt (standardRootLogCorrection t g) (f w+q w) w := by
    exact hasDerivAt_standardRootLogCorrection t g w
      (fun he => hnonzero w hw (sub_eq_zero.mpr he.symm))
      (sourceStandardRoot_radicand_mem_slitPlane hp hp1 ψ n w hw)
  have hsum := curveIntegral_eq_sub_of_primitive (fun w => f w+q w) (standardRootLogCorrection t g) A
    hprim γ hγ (fun u hu => by simpa only [Path.extend_apply γ hu,A,Set.mem_compl_iff] using havoid ⟨u,hu⟩)
    (((hf.add hq).smul continuousOn_const).curveIntegrable_of_contDiffOn hγ havoid)
  simp only [sub_self] at hsum
  have heq : holomorphicOneForm (fun w => f w+q w) = holomorphicOneForm f+holomorphicOneForm q := by
    ext w
    simp only [Pi.add_apply,add_apply,holomorphicOneForm_apply]
    ring
  rw [heq,curveIntegral_add hfint hqint] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

end NLS.ZakharovShabat
