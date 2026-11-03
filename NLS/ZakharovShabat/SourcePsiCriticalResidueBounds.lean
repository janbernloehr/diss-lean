import NLS.ZakharovShabat.SourcePsiCriticalInterpolation
import NLS.ComplexAnalysis.SimplePoleCircleResidue
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.FiniteHeadTailBound

/-! # Actual Hilbert membership of canonical critical residues

The large separated-exterior estimate bounds each distant residue by
its actual small-circle integral. The resulting reciprocal-index tail
and a finite head give genuine l2 membership.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourcePsiCriticalResidue_reciprocal_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∀ m : ℤ, K < m.natAbs →
      ‖sourcePsiCriticalResidue hp hp1 n a φ m‖ ≤ 4/(m.natAbs:ℝ) := by
  obtain ⟨R,_,hR⟩ := exists_threshold_sourcePsiCandidate_criticalQuotient_le hp hp1 n a φ
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨M,hM⟩ := exists_nat_gt ((R+Real.pi/4)/Real.pi)
  let Nc := canonicalCriticalCutoff hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  refine ⟨max Nc (max M 1),?_⟩
  intro m hm
  have hNc : Nc < m.natAbs := (le_max_left _ _).trans_lt hm
  have hMm : M ≤ m.natAbs := (le_max_left M 1).trans ((le_max_right _ _).trans hm.le)
  have hmp : 0 < (m.natAbs:ℝ) := by
    have h1 : 1 ≤ m.natAbs := (le_max_right M 1).trans ((le_max_right _ _).trans hm.le)
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) h1
  let β := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  have hlabel := (canonicalCriticalPoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).1
  obtain ⟨hb,hzero,_,hunique⟩ := hlabel.distant m hNc
  have hsimple := discriminant_second_derivative_ne_zero_at_critical_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hr) β hzero
  have hf : AnalyticOnNhd ℂ (fun z => sourcePsiCandidate n (z,a))
      (closedBall ((Real.pi:ℂ)*m) (Real.pi/4)) := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hg := (analyticOnNhd_discriminant_derivative hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).mono
    (subset_univ (closedBall ((Real.pi:ℂ)*m) (Real.pi/4)))
  have hpoint (z : ℂ) (hz : z ∈ sphere ((Real.pi:ℂ)*m) (Real.pi/4)) :
      ‖sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z‖ ≤
        16/(Real.pi*(m.natAbs:ℝ)) := by
    have hdist : ‖z-(Real.pi:ℂ)*m‖ = Real.pi/4 := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hcenter : ‖(Real.pi:ℂ)*m‖ = Real.pi*(m.natAbs:ℝ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
    have htri := norm_sub_le z (z-(Real.pi:ℂ)*m)
    rw [sub_sub_cancel,hdist,hcenter] at htri
    have hMreal : R+Real.pi/4 < (M:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hM)
    have hMmreal : (M:ℝ) ≤ (m.natAbs:ℝ) := by exact_mod_cast hMm
    have hzR : R ≤ ‖z‖ := by nlinarith [Real.pi_pos]
    have h1real : 1 ≤ (m.natAbs:ℝ) := by exact_mod_cast (show 1 ≤ m.natAbs by omega)
    have hhalf : Real.pi*(m.natAbs:ℝ)/2 ≤ ‖z‖ := by nlinarith [Real.pi_pos]
    have hnorm : 0 < ‖z‖ := (half_pos (mul_pos Real.pi_pos hmp)).trans_le hhalf
    have he := (hR z hzR (freeSphere_separated (by positivity : 0 < Real.pi/4) le_rfl m hz)).2
    apply he.trans
    apply (div_le_div_iff₀ hnorm (mul_pos Real.pi_pos hmp)).mpr
    nlinarith
  have hi := norm_simpleQuotientResidue_le (by positivity : 0 < Real.pi/4) hf hg hb hzero hsimple
    (fun z hz h => (hunique z hz).mp h) hpoint
  change ‖sourcePsiCriticalResidue hp hp1 n a φ m‖ ≤ _ at hi
  have hcalc : (Real.pi/4)*(16/(Real.pi*(m.natAbs:ℝ))) = 4/(m.natAbs:ℝ) := by
    field_simp
    ring
  rwa [hcalc] at hi

theorem memℓp_sourcePsiCriticalResidue_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (sourcePsiCriticalResidue hp hp1 n a φ) 2 := by
  obtain ⟨K,hK⟩ := exists_sourcePsiCriticalResidue_reciprocal_bound hp hp1 n a φ hr
  let S := Finset.Icc (-(K:ℤ)) K
  apply (Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (p := 2) (sourcePsiCriticalResidue hp hp1 n a φ) (sourcePsiCriticalResidue hp hp1 n a φ) S
    (Coeff.puncturedLattice 2 (by norm_num)) 0 4 (by norm_num) (fun _ _ => le_rfl) ?_).1
  intro m hm
  have hKm : K < m.natAbs := by dsimp only [S] at hm; simp only [Finset.mem_Icc] at hm; omega
  have hm0 : m ≠ 0 := by intro h; simp only [h,Int.natAbs_zero] at hKm; omega
  have hb := hK m hKm
  simpa only [Coeff.puncturedLattice_apply,if_neg hm0,norm_inv,Complex.norm_intCast,
    lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,div_eq_mul_inv,Nat.cast_natAbs,Int.cast_abs] using hb

end NLS.ZakharovShabat
