import NLS.KdV.ClassicalUniformPeriodEntries
import NLS.KdV.HighEnergyContourSeparation
import NLS.ComplexAnalysis.RationalCircleIntegrationByParts

/-! # Actual high period entries as primitive integrals

The filled numerator identity and the constructed primitive give the
integration by parts formula with its exact coefficient n. The denominator
is squared, as needed for summable off-diagonal estimates. No primitive
extension through a spectral gap is required.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHillUniformHighPeriod_eq_primitive (N : ℕ) (n k : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (shift : ℂ)
    (hfactor : ∀ lam : ℂ,
      (lam-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (lam,q) =
        (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) lam)
    (hcover : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      (z^2,q) ∈ classicalHillContinuationDomain)
    (hne : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      z^2-classicalHillUniformCriticalPoint N n q ≠ 0) :
    classicalHillUniformHighPeriod N n k q = (n : ℂ) *
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (classicalHillContinuedPrimitive (z^2,q)+shift)*(2*z)/
          (z^2-classicalHillUniformCriticalPoint N n q)^2 := by
  let H : ℂ → ℂ := fun z => classicalHillContinuedPrimitive (z^2,q)+shift
  let G : ℂ → ℂ := fun z => z^2-classicalHillUniformCriticalPoint N n q
  have hH : AnalyticOnNhd ℂ H (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillContinuedPrimitive (z^2,q) (hcover z hz)).comp
      (f := fun w : ℂ => (w^2,q))
      ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hG : AnalyticOnNhd ℂ G (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :=
    (analyticOnNhd_id.pow 2).sub analyticOnNhd_const
  have hDG (z : ℂ) : deriv G z = 2*z := by
    exact ((hasDerivAt_id z).pow 2 |>.sub_const _).deriv.trans (by simp)
  have hDH (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      deriv H z = (deriv (classicalHillDiscriminant q) (z^2)/
        classicalHillContinuedRoot (z^2,q))*(2*z) := by
    have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
      simpa using! (hasDerivAt_id z).pow 2
    exact ((hasDerivAt_classicalHillContinuedPrimitive (z^2,q)
      (hcover z hz)).comp z hsq |>.add_const shift).deriv
  have hp := circleIntegral_deriv_div_eq H G _ _ (by positivity) hH hG hne
  have hpoint (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      (classicalHillUniformNumerator N n (z^2,q)/classicalHillContinuedRoot (z^2,q))*(2*z) =
        (2*(n : ℂ)*Real.pi)*(deriv H z/G z) := by
    have hb : classicalHillUniformNumerator N n (z^2,q) =
        (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) (z^2)/G z := by
      apply (eq_div_iff (hne z hz)).mpr
      exact (mul_comm _ _).trans (hfactor (z^2))
    rw [hb,hDH z hz]
    simp only [div_eq_mul_inv]
    ring
  unfold classicalHillUniformHighPeriod
  rw [circleIntegral.integral_congr (by positivity) hpoint,circleIntegral.integral_const_mul,hp]
  simp_rw [hDG]
  change (2*(Real.pi : ℂ))⁻¹ * ((2*(n : ℂ)*Real.pi)*
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), H z*(2*z)/(G z)^2)) = _
  rw [← mul_assoc]
  congr 1
  field_simp

/-- Quantitative scalar estimate from a bound on the shifted primitive.
Uniform primitive bounds still have to be proved before this becomes a
bounded-operator estimate for the whole period matrix. -/
theorem norm_classicalHillUniformHighPeriod_le (N : ℕ) (n k : ℕ+) (hnk : n ≠ k)
    (q : NLS.LinearVolterra.Curve ℂ) (shift : ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ lam : ℂ,
      (lam-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (lam,q) =
        (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) lam)
    (hcover : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      (z^2,q) ∈ classicalHillContinuationDomain)
    (hsep : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| ≤
        ‖z^2-classicalHillUniformCriticalPoint N n q‖)
    (hprim : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      ‖classicalHillContinuedPrimitive (z^2,q)+shift‖ ≤ A) :
    ‖classicalHillUniformHighPeriod N n k q‖ ≤
      (20/Real.pi)*(n : ℝ)*(k : ℝ)*A/|(k : ℝ)^2-(n : ℝ)^2|^2 := by
  let D : ℝ := |(k : ℝ)^2-(n : ℝ)^2|
  have hD : 0 < D := by
    apply abs_pos.mpr
    rw [sq_sub_sq]
    apply mul_ne_zero (by positivity)
    apply sub_ne_zero.mpr
    intro he
    apply hnk
    exact_mod_cast he.symm
  have hden : 0 < Real.pi^2/4*D := by positivity
  have hne (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      z^2-classicalHillUniformCriticalPoint N n q ≠ 0 :=
    norm_pos_iff.mp (hden.trans_le (hsep z hz))
  rw [classicalHillUniformHighPeriod_eq_primitive N n k q shift hfactor hcover hne,norm_mul]
  have hi : ‖∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (classicalHillContinuedPrimitive (z^2,q)+shift)*(2*z)/
        (z^2-classicalHillUniformCriticalPoint N n q)^2‖ ≤
      2*Real.pi*(Real.pi/4)*((40/Real.pi^3)*A*(k : ℝ)/D^2) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const (by positivity)
    intro z hz
    have hzc : ‖z-(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi/4 := mem_sphere_iff_norm.mp hz
    have hcn : ‖(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi*(k : ℝ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_natCast]
    have ht := norm_add_le (z-(Real.pi : ℂ)*(k : ℕ)) ((Real.pi : ℂ)*(k : ℕ))
    rw [sub_add_cancel,hzc,hcn] at ht
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    have htwo : ‖(2 : ℂ)*z‖ ≤ (5*Real.pi/2)*(k : ℝ) := by
      rw [norm_mul]
      norm_num only [norm_ofNat]
      nlinarith [Real.pi_pos]
    calc
      _ = ‖classicalHillContinuedPrimitive (z^2,q)+shift‖*‖(2 : ℂ)*z‖/
          ‖z^2-classicalHillUniformCriticalPoint N n q‖^2 := by
        rw [norm_div,norm_mul,norm_pow]
      _ ≤ A*((5*Real.pi/2)*(k : ℝ))/(Real.pi^2/4*D)^2 := by
        gcongr
        · exact hprim z hz
        · exact hsep z hz
      _ = (40/Real.pi^3)*A*(k : ℝ)/D^2 := by field_simp; ring
  have hn : ‖(n : ℂ)‖ = (n : ℝ) := by simp only [Complex.norm_natCast]
  rw [hn]
  calc
    _ ≤ (n : ℝ)*(2*Real.pi*(Real.pi/4)*((40/Real.pi^3)*A*(k : ℝ)/D^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by change _ = (20/Real.pi)*(n : ℝ)*(k : ℝ)*A/D^2; field_simp; ring

/-- The actual infinite matrix admits the squared-denominator formula
throughout one uniform off-diagonal tail on the same neighborhood where
all its scalar entries are analytic. Every spectral input is constructed. -/
theorem exists_classicalHill_uniform_period_tail_formula :
    ∃ N M : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      0 < N ∧ N ≤ M ∧ IsOpen V ∧ 0 ∈ V ∧
      (∀ n k : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformPeriod N n k) V ∧
        classicalHillUniformPeriod N n k 0 = if n = k then 1 else 0) ∧
      (∀ n : ℕ+, ∀ q ∈ V, ∀ lam : ℂ,
        (lam-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (lam,q) =
          (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) lam) ∧
      ∀ n k : ℕ+, M < (n : ℕ) → M < (k : ℕ) → n ≠ k → ∀ q ∈ V,
        (∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          Real.pi^2/4 * |(k : ℝ)^2-(n : ℝ)^2| ≤
            ‖z^2-classicalHillUniformCriticalPoint N n q‖) ∧
        classicalHillUniformPeriod N n k q = (n : ℂ) *
          ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)*(2*z)/
              (z^2-classicalHillUniformCriticalPoint N n q)^2 := by
  obtain ⟨N,W,hN,hW,h0W,hfactor,hentries⟩ :=
    exists_analytic_classicalHill_uniform_period_entries
  obtain ⟨L,U,_,hU,h0U,hhigh⟩ := exists_analytic_classicalHillHighCriticalPoints 0
  refine ⟨N,max N L,W ∩ U,hN,le_max_left _ _,hW.inter hU,⟨h0W,h0U⟩,
    fun n k => ⟨((hentries n k).1.mono inter_subset_left),(hentries n k).2⟩,
    fun n q hq => hfactor n q hq.1,?_⟩
  intro n k hn hk hnk q hq
  have hnN := (le_max_left N L).trans_lt hn
  have hkN := (le_max_left N L).trans_lt hk
  have hnL := (le_max_right N L).trans_lt hn
  have hkL := (le_max_right N L).trans_lt hk
  have he : classicalHillUniformCriticalPoint N n q = classicalHillFrequencyCritical q n ^ 2 :=
    if_neg (Nat.not_le_of_gt hnN)
  have hcrit := ball_subset_closedBall ((hhigh n hnL).2.2 q hq.2).1
  refine ⟨?_,?_⟩
  · intro z hz
    rw [he]
    exact highEnergyContour_separation n k hnk z _ hz hcrit
  rw [classicalHillUniformPeriod,if_neg (Nat.not_le_of_gt hkN)]
  apply classicalHillUniformHighPeriod_eq_primitive N n k q _ (hfactor n q hq.1)
    ((hhigh k hkL).2.2 q hq.2).2.2.2.2
  intro z hz
  rw [he]
  exact highEnergyContour_sub_sq_ne_zero n k hnk z _ hz hcrit

end NLS.KdV
