import NLS.ZakharovShabat.SourceDistantCriticalComplexNeighborhood
import NLS.KdV.ClassicalCriticalPointBranch
import NLS.KdV.ClassicalContourCoverage
import NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood

/-! # One analytic neighborhood for the actual high Hill critical points

Transfer the established complex ZS critical labeling through the actual
constant-upper coefficient embedding and lambda=z². No real-type condition
on that embedding is imposed. One cutoff and one potential neighborhood
support every high energy critical point, its simplicity and unique label,
and the corresponding continued-root contours.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- Undoubled period-one Fourier coefficients of the actual pair (-1,-q). -/
def classicalHillSourceCoefficients (q : NLS.LinearVolterra.Curve ℂ) : CoeffPair 2 :=
  sourcePhysicalL2Equiv.symm (continuousPotentialL2CLM (constantUpperPotential q))

theorem analyticOnNhd_classicalHillSourceCoefficients :
    AnalyticOnNhd ℂ classicalHillSourceCoefficients univ := by
  intro q _
  have hc := (continuousPotentialL2CLM.analyticAt (constantUpperPotential q)).comp
    (analyticOnNhd_constantUpperPotential q (mem_univ _))
  exact (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt _).comp hc

/-- The existing canonical frequency critical coordinate for the actual Hill trace. -/
def classicalHillFrequencyCritical (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) : ℂ :=
  canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential q)
    (classicalHillCoefficientPotential_even q) (n : ℤ)

/-- The corresponding actual energy critical point. -/
def classicalHillHighCriticalPoint (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) : ℂ :=
  classicalHillFrequencyCritical q n ^ 2

theorem classicalHill_frequency_derivative_eq (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q)) z =
      (2*z)*deriv (classicalHillDiscriminant q) (z^2) := by
  have he : canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q) =
      (fun w : ℂ => classicalHillDiscriminant q (w^2)) := by
    funext w
    rw [classicalHillDiscriminant_sq, canonicalDiscriminant_classicalHillCoefficientPotential]
  rw [he]
  have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hd := ((analyticOnNhd_classicalHillDiscriminant q (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z hsq
  change HasDerivAt (fun w : ℂ => classicalHillDiscriminant q (w^2))
    (deriv (classicalHillDiscriminant q) (z^2)*(2*z)) z at hd
  exact hd.deriv.trans (by ring)

theorem classicalHill_frequency_second_derivative_eq (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    deriv (deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q))) z =
      2*deriv (classicalHillDiscriminant q) (z^2)+
        4*z^2*deriv (deriv (classicalHillDiscriminant q)) (z^2) := by
  have he : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q)) =
      (fun w : ℂ => (2*w)*deriv (classicalHillDiscriminant q) (w^2)) :=
    funext (classicalHill_frequency_derivative_eq q)
  rw [he]
  have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hd := (((analyticOnNhd_classicalHillDiscriminant q (z^2) (mem_univ _)).deriv).differentiableAt.hasDerivAt).comp z hsq
  change HasDerivAt (fun w : ℂ => deriv (classicalHillDiscriminant q) (w^2))
    (deriv (deriv (classicalHillDiscriminant q)) (z^2)*(2*z)) z at hd
  have htwo : HasDerivAt (fun w : ℂ => 2*w) 2 z := by
    simpa using! (hasDerivAt_id z).const_mul 2
  have hp := htwo.mul hd
  change HasDerivAt (fun w : ℂ => (2*w)*deriv (classicalHillDiscriminant q) (w^2))
    (2*deriv (classicalHillDiscriminant q) (z^2)+
      (2*z)*(deriv (deriv (classicalHillDiscriminant q)) (z^2)*(2*z))) z at hp
  exact hp.deriv.trans (by ring)

/-- At every complex continuous potential, the entire high critical family
is analytic on one neighborhood. All actual critical points in each mapped
closed high disc have the selected label, and the energy zeros remain simple. -/
theorem exists_analytic_classicalHillHighCriticalPoints (q0 : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ q0 ∈ V ∧
      ∀ n : ℕ+, N < (n : ℕ) →
        AnalyticOnNhd ℂ (fun q => classicalHillFrequencyCritical q n) V ∧
        AnalyticOnNhd ℂ (fun q => classicalHillHighCriticalPoint q n) V ∧
        ∀ q ∈ V,
          classicalHillFrequencyCritical q n ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) ∧
          deriv (classicalHillDiscriminant q) (classicalHillHighCriticalPoint q n) = 0 ∧
          deriv (deriv (classicalHillDiscriminant q)) (classicalHillHighCriticalPoint q n) ≠ 0 ∧
          (∀ lam ∈ (fun z : ℂ => z^2) '' closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
            deriv (classicalHillDiscriminant q) lam = 0 ↔ lam = classicalHillHighCriticalPoint q n) ∧
          ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
            (z^2,q) ∈ classicalHillContinuationDomain := by
  obtain ⟨Na,Ua,hNa,hUa,hqa,ha⟩ :=
    exists_local_source_distantCanonicalCriticalPoints_analytic_complex (by simp) (by norm_num)
      (classicalHillSourceCoefficients q0)
  obtain ⟨Nl,hNl,Ul,hUl,_,hql,_,R,hR,hlabel⟩ :=
    exists_uniform_canonicalCriticalPoints (by simp) (by norm_num) (classicalHillCoefficientPotential q0)
  obtain ⟨Nc,Uc,hNc,hUc,hqc,hcover⟩ := exists_classicalHill_high_contour_neighborhood q0
  let V := (classicalHillSourceCoefficients ⁻¹' Ua) ∩
    (classicalHillCoefficientPotential ⁻¹' Ul) ∩ Uc
  have hV : IsOpen V :=
    ((hUa.preimage analyticOnNhd_classicalHillSourceCoefficients.continuous).inter
      (hUl.preimage continuous_classicalHillCoefficientPotential)).inter hUc
  refine ⟨max (max Na Nl) Nc,V,hNa.trans_le ((le_max_left Na Nl).trans (le_max_left _ _)),hV,
    ⟨⟨hqa,hql⟩,hqc⟩,?_⟩
  intro n hn
  have hna : Na < (n : ℤ).natAbs := by
    simpa using ((le_max_left Na Nl).trans (le_max_left (max Na Nl) Nc)).trans_lt hn
  have hnl : Nl < (n : ℤ).natAbs := by
    simpa using ((le_max_right Na Nl).trans (le_max_left (max Na Nl) Nc)).trans_lt hn
  have hnc : Nc < (n : ℕ) := (le_max_right _ _).trans_lt hn
  have hbranch (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
      AnalyticAt ℂ (fun a => classicalHillFrequencyCritical a n) q := by
    have hs := (ha _ hq.1.1 (n : ℤ) hna).1
    simpa only [classicalHillFrequencyCritical, classicalHillCoefficientPotential,
      classicalHillSourceCoefficients, Function.comp_def] using!
      hs.comp (f := classicalHillSourceCoefficients)
        (analyticOnNhd_classicalHillSourceCoefficients q (mem_univ _))
  refine ⟨hbranch,fun q hq => (hbranch q hq).pow 2,?_⟩
  intro q hq
  have hl := ((hlabel _ hq.1.2 (classicalHillCoefficientPotential_even q)).1.distant (n : ℤ) hnl)
  have hmem : classicalHillFrequencyCritical q n ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    simpa only [classicalHillFrequencyCritical, Int.cast_natCast] using! hl.1
  have hz0 : classicalHillFrequencyCritical q n ≠ 0 := by
    intro hzero
    have hp := re_pos_of_high_closedBall (n : ℕ) n.property _ (ball_subset_closedBall hmem)
    simp only [hzero, zero_re, lt_self_iff_false] at hp
  have hcrit : deriv (classicalHillDiscriminant q) (classicalHillHighCriticalPoint q n) = 0 := by
    have he := classicalHill_frequency_derivative_eq q (classicalHillFrequencyCritical q n)
    have hc : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q))
        (classicalHillFrequencyCritical q n) = 0 := hl.2.1
    rw [hc] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) hz0)
  have hsimple : deriv (deriv (classicalHillDiscriminant q)) (classicalHillHighCriticalPoint q n) ≠ 0 := by
    have hs := (ha _ hq.1.1 (n : ℤ) hna).2
    have hs' : deriv (deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q)))
        (classicalHillFrequencyCritical q n) ≠ 0 := by
      simpa only [classicalHillFrequencyCritical, classicalHillCoefficientPotential,
        classicalHillSourceCoefficients] using! hs
    intro hzero
    apply hs'
    rw [classicalHill_frequency_second_derivative_eq]
    change 2*deriv (classicalHillDiscriminant q) (classicalHillHighCriticalPoint q n)+
      4*(classicalHillFrequencyCritical q n)^2*
        deriv (deriv (classicalHillDiscriminant q)) (classicalHillHighCriticalPoint q n) = 0
    rw [hcrit,hzero]
    ring
  refine ⟨hmem,hcrit,hsimple,?_,fun z hz => hcover q hq.2 (n : ℕ) hnc z hz⟩
  rintro lam ⟨z,hz,rfl⟩
  constructor
  · intro hzero
    have hf : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q)) z = 0 := by
      rw [classicalHill_frequency_derivative_eq,hzero,mul_zero]
    have heq := (hl.2.2.2 z (by simpa only [Int.cast_natCast] using hz)).mp hf
    exact congrArg (fun z : ℂ => z^2) heq
  · intro he
    exact he ▸ hcrit

end NLS.KdV
