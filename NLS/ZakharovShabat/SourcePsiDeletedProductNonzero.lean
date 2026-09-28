import NLS.ZakharovShabat.SourcePsiDiagonalRootCancellation
import NLS.ZakharovShabat.CriticalPointProducts

/-!
# Zeros of the deleted psi numerator

Quarter-π localization separates the displaced roots and makes their
range closed. The complete entire product has exactly these zeros.
Moving the omitted root while leaving its deleted product fixed then
shows that the latter has no zeros away from all retained roots.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Distinct roots localized within π/4 of their own free centers
remain at least π/2 apart. -/
theorem half_pi_le_dist_displacedRoots_of_quarter_localized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4)
    (j k : ℤ) (hjk : j ≠ k) :
    Real.pi/2 ≤ dist (displacedRoots a j) (displacedRoots a k) := by
  have hfree : Real.pi ≤ ‖(Real.pi : ℂ)*j-(Real.pi : ℂ)*k‖ := by
    rw [norm_free_center_sub]
    have hidx : (1:ℝ) ≤ |((j-k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjk)
    nlinarith [Real.pi_pos]
  have heq : (Real.pi : ℂ)*j-(Real.pi : ℂ)*k =
      (displacedRoots a j-displacedRoots a k)-a j+a k := by
    simp only [displacedRoots]
    ring
  have htri : ‖(Real.pi : ℂ)*j-(Real.pi : ℂ)*k‖ ≤
      ‖displacedRoots a j-displacedRoots a k‖+‖a j‖+‖a k‖ := by
    rw [heq]
    calc
      _ ≤ ‖(displacedRoots a j-displacedRoots a k)-a j‖+‖a k‖ :=
        norm_add_le _ _
      _ ≤ (‖displacedRoots a j-displacedRoots a k‖+‖a j‖)+‖a k‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by ring
  rw [dist_eq_norm]
  nlinarith [hloc j, hloc k]

/-- The range of quarter-π localized displaced roots is closed. -/
theorem isClosed_range_displacedRoots_of_quarter_localized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4) :
    IsClosed (Set.range (displacedRoots a)) := by
  apply Metric.isClosed_of_pairwise_le_dist
    (by positivity : (0:ℝ) < Real.pi/2)
  rintro x ⟨j,rfl⟩ y ⟨k,rfl⟩ hne
  have hjk : j ≠ k := by
    intro he
    exact hne (by rw [he])
  exact half_pi_le_dist_displacedRoots_of_quarter_localized a hloc j k hjk

/-- The full root product has exactly the displaced roots as zeros
under quarter-π localization. -/
theorem jointSingleSpectralProduct_eq_zero_iff_of_quarter_localized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a : Coeff p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4) (z : ℂ) :
    jointSingleSpectralProduct (z,a) = 0 ↔
      ∃ k : ℤ, displacedRoots a k = z := by
  exact entireSingleSpectralProduct_eq_zero_iff hp
    (displacedRoots a) (memℓp_displacedRoots a)
      (isClosed_range_displacedRoots_of_quarter_localized a hloc) z

/-- Omitting the selected root leaves a numerator with no zero
away from every other displaced root. This also covers the selected
root itself: moving only that root leaves the deleted product fixed. -/
theorem jointDeletedSingleSpectralProduct_ne_zero_of_quarter_localized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (z : ℂ) (a : Coeff p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4)
    (hother : ∀ k : ℤ, k ≠ m → z ≠ displacedRoots a k) :
    jointDeletedSingleSpectralProduct m (z,a) ≠ 0 := by
  let cf : ℂ := (Real.pi : ℂ)*m
  let d : ℂ := if z = cf then (Real.pi : ℂ)/8 else 0
  let b : Coeff p := a+lp.single p m (d-a m)
  have hbm : b m = d := by
    change (a+lp.single p m (d-a m) : Coeff p) m = d
    simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply_self]
    ring
  have hbk (k : ℤ) (hkm : k ≠ m) : b k = a k := by
    change (a+lp.single p m (d-a m) : Coeff p) k = a k
    simp only [lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ hkm,add_zero]
  have hdBound : ‖d‖ ≤ Real.pi/4 := by
    by_cases hzcf : z = cf
    · simp only [d,if_pos hzcf, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
      nlinarith [Real.pi_pos]
    · simp only [d,if_neg hzcf,norm_zero]
      positivity
  have hlocb : ∀ k : ℤ, ‖b k‖ ≤ Real.pi/4 := by
    intro k
    by_cases hkm : k = m
    · subst k
      simpa only [hbm] using hdBound
    · rw [hbk k hkm]
      exact hloc k
  have hrootm : displacedRoots b m ≠ z := by
    change cf+b m ≠ z
    rw [hbm]
    by_cases hzcf : z = cf
    · rw [hzcf]
      simp only [d,if_pos hzcf]
      intro he
      have hπ : (Real.pi : ℂ)/8 = 0 := by
        exact add_left_cancel (by simpa only [add_zero] using he :
          cf+(Real.pi : ℂ)/8 = cf+0)
      exact (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by norm_num)) hπ
    · simpa only [d,if_neg hzcf,add_zero] using (Ne.symm hzcf)
  have hprod : jointSingleSpectralProduct (z,b) ≠ 0 := by
    intro hzero
    obtain ⟨k,hk⟩ :=
      (jointSingleSpectralProduct_eq_zero_iff_of_quarter_localized
        hp b hlocb z).mp hzero
    by_cases hkm : k = m
    · subst k
      exact hrootm hk
    · rw [show displacedRoots b k = displacedRoots a k by
        simp only [displacedRoots,hbk k hkm]] at hk
      exact hother k hkm hk.symm
  have hdeletedb : jointDeletedSingleSpectralProduct m (z,b) ≠ 0 := by
    intro hzero
    have hfactor := jointSingleSpectralProduct_eq_deleted hp hp1 m (z,b)
    rw [hzero,mul_zero] at hfactor
    exact hprod hfactor
  have heq := jointDeletedSingleSpectralProduct_add_single_deleted
    m z a (d-a m)
  exact heq ▸ hdeletedb

/-- The corresponding omitted-root quotient is nonzero wherever
its standard denominator is defined and all retained roots are absent. -/
theorem sourceSingleRootQuotientJointProduct_ne_zero_of_quarter_localized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (z : ℂ) (a : Coeff p) (ψ : CoeffPair p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4)
    (hother : ∀ k : ℤ, k ≠ m → z ≠ displacedRoots a k)
    (hdom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) ≠ 0 := by
  exact div_ne_zero
    (jointDeletedSingleSpectralProduct_ne_zero_of_quarter_localized
      hp hp1 m z a hloc hother)
    (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hdom)

/-- A selected free quarter-π disc avoids every root assigned to a
different quarter-π disc. -/
theorem selected_quarter_ball_avoids_other_displacedRoots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4)
    (m : ℤ) (z : ℂ)
    (hz : z ∈ ball ((Real.pi : ℂ)*m) (Real.pi/4))
    (k : ℤ) (hkm : k ≠ m) :
    z ≠ displacedRoots a k := by
  intro he
  have hfree : Real.pi ≤
      dist ((Real.pi : ℂ)*m) ((Real.pi : ℂ)*k) := by
    rw [dist_eq_norm,norm_free_center_sub]
    have hidx : (1:ℝ) ≤ |((m-k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hkm))
    nlinarith [Real.pi_pos]
  have htri := dist_triangle ((Real.pi : ℂ)*m) z ((Real.pi : ℂ)*k)
  have hzdist : dist ((Real.pi : ℂ)*m) z < Real.pi/4 := by
    simpa only [dist_comm] using (mem_ball.mp hz)
  have hkdist : dist z ((Real.pi : ℂ)*k) ≤ Real.pi/4 := by
    rw [he,dist_eq_norm]
    simpa only [displacedRoots,add_sub_cancel_left] using hloc k
  nlinarith [Real.pi_pos]

/-- The regular quotient has no zeros on the selected free disc
whenever the other standard gap cuts avoid that disc. -/
theorem sourceSingleRootQuotientJointProduct_ne_zero_on_selected_quarter_ball
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (z : ℂ) (a : Coeff p) (ψ : CoeffPair p)
    (hloc : ∀ k : ℤ, ‖a k‖ ≤ Real.pi/4)
    (hz : z ∈ ball ((Real.pi : ℂ)*m) (Real.pi/4))
    (hdom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) ≠ 0 := by
  exact sourceSingleRootQuotientJointProduct_ne_zero_of_quarter_localized
    hp hp1 m z a ψ hloc
      (fun k hkm => selected_quarter_ball_avoids_other_displacedRoots
        a hloc m z hz k hkm) hdom

end NLS.ZakharovShabat
