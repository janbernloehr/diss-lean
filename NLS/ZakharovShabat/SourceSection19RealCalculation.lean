import NLS.ZakharovShabat.SourceCanonicalRootRealBand
import NLS.ZakharovShabat.RealGapDiscriminantLevels
import NLS.ZakharovShabat.CanonicalCriticalInterlacing
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The real-gap and real-band assertions in Section 19

The signed discriminant minus the positive root has a strictly positive
minimum on every closed real gap. On the closed band between consecutive
gaps, the oppositely signed discriminant is strictly increasing from -2
to 2. These statements include all signed indices and collapsed adjacent
gaps, and use the actual canonical spectral data.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The positive companion expression in the proof of Lemma 19.1(i). -/
def sourceRealGapCompanion (hp : p ≠ ⊤) (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^n*(canonicalDiscriminant hp (periodOnePotential ψ) x).re -
    Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4)

/-- Positivity holds at both endpoints as well as in the gap interior. -/
theorem sourceRealGapCompanion_pos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 < sourceRealGapCompanion hp ψ n x := by
  let a := (-1 : ℝ)^n*(canonicalDiscriminant hp (periodOnePotential ψ) x).re
  have ha : 2 ≤ a := signed_discriminant_ge_two_on_canonicalGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) n x hx
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  have ha2 : a^2 = (canonicalDiscriminant hp (periodOnePotential ψ) x).re^2 := by
    dsimp [a]
    rw [mul_pow,hs,one_mul]
  have hrad : 0 ≤ (canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4 := by
    nlinarith
  have hroot := Real.sq_sqrt hrad
  have hnonneg := Real.sqrt_nonneg ((canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4)
  change 0 < a-Real.sqrt ((canonicalDiscriminant hp (periodOnePotential ψ) x).re^2-4)
  nlinarith

/-- The displayed minimum is attained and strictly positive, including
when the selected gap consists of one point. -/
theorem sourceRealGapCompanion_positive_minimum (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    ∃ x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
      0 < sourceRealGapCompanion hp ψ n x ∧
      ∀ y ∈ Icc
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
        sourceRealGapCompanion hp ψ n x ≤ sourceRealGapCompanion hp ψ n y := by
  have hD : Continuous (fun x : ℝ => (canonicalDiscriminant hp (periodOnePotential ψ) x).re) :=
    continuous_re.comp ((continuousOn_univ.mp
      (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem ψ)).continuousOn).comp
        continuous_ofReal)
  have hc : Continuous (sourceRealGapCompanion hp ψ n) :=
    (continuous_const.mul hD).sub (Real.continuous_sqrt.comp ((hD.pow 2).sub continuous_const))
  have hab := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc.continuousOn
  exact ⟨x,hx,sourceRealGapCompanion_pos hp hp1 ψ hψ n x hx,hmin⟩

/-- No critical point lies in an open band: every critical point belongs
to a closed gap, and the band avoids all such gaps. -/
theorem sourceDiscriminant_deriv_ne_zero_on_realBand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 ψ n) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x : ℂ) ≠ 0 := by
  intro hz
  obtain ⟨m,hm⟩ := (canonicalCriticalPoints_exhaustive hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (x : ℂ)).mp hz
  have hgap := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) m
  rw [hm,ofReal_re] at hgap
  exact sourceRealBand_subset_rootDomain hp hp1 ψ hψ n x hx m
    (sourcePeriodicSegment_mem_of_realIcc hp hp1 ψ hψ m x hgap)

/-- The band orientation has the exact endpoint levels -2 and 2. -/
theorem sourceSignedDiscriminant_realBand_endpoints (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    let f := fun x : ℝ => (-1 : ℝ)^(n+1)*(canonicalDiscriminant hp (periodOnePotential ψ) x).re
    f (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re = -2 ∧
    f (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1)).re = 2 := by
  have hreal := isRealType_periodOnePotential ψ hψ
  have hr : (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re : ℝ) : ℂ) =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n :=
    Complex.ext rfl (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal n).2.symm
  have hl : (((canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1)).re : ℝ) : ℂ) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1) :=
    Complex.ext rfl (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal (n+1)).1.symm
  dsimp only
  rw [hr,hl,(canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal n).2,
    (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal (n+1)).1]
  by_cases hn : n % 2 = 0
  · have hn' : (n+1) % 2 ≠ 0 := by omega
    simp [neg_one_zpow_eq_ite,Int.odd_iff,hn,hn']
  · have hn' : (n+1) % 2 = 0 := by omega
    simp [neg_one_zpow_eq_ite,Int.odd_iff,hn,hn']

/-- The signed discriminant is strictly increasing on the whole closed
band, not just confined between its endpoint levels in the interior. -/
theorem sourceSignedDiscriminant_strictMonoOn_realBand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    StrictMonoOn (fun x : ℝ => (-1 : ℝ)^(n+1)*(canonicalDiscriminant hp (periodOnePotential ψ) x).re)
      (Icc (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1)).re) := by
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n+1)).re
  let f := fun x : ℝ => (-1 : ℝ)^(n+1)*(canonicalDiscriminant hp (periodOnePotential ψ) x).re
  let f' := fun x : ℝ => (-1 : ℝ)^(n+1)*(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) x).re
  have hd (x : ℝ) : HasDerivAt f (f' x) x :=
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem ψ) x
      (mem_univ _)).differentiableAt.hasDerivAt.real_of_complex).const_mul _
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hnz (x : ℝ) (hx : x ∈ Ioo a b) : f' x ≠ 0 := by
    apply mul_ne_zero (zpow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
    intro hz
    apply sourceDiscriminant_deriv_ne_zero_on_realBand hp hp1 ψ hψ n x hx
    exact Complex.ext hz (discriminant_derivative_im_eq_zero_of_realType hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) x)
  have hlt (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) : f x ≠ f y := by
    intro he
    obtain ⟨z,hz,hzero⟩ := exists_hasDerivAt_eq_zero hxy
      hc.continuousOn he (fun t _ => hd t)
    exact hnz z ⟨hx.1.trans_lt hz.1,hz.2.trans_le hy.2⟩ hzero
  have hinj : InjOn f (Icc a b) := by
    intro x hx y hy he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt x y hx hy h he
    · exact hlt y x hy hx h he.symm
  have hab : a < b := canonicalPeriodicRight_re_lt_next_left hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) n
  have hend := sourceSignedDiscriminant_realBand_endpoints hp hp1 ψ hψ n
  change f a = -2 ∧ f b = 2 at hend
  exact ContinuousOn.strictMonoOn_of_injOn_Icc hab.le
    (by change f a ≤ f b; rw [hend.1,hend.2]; norm_num) hc.continuousOn hinj

end NLS.ZakharovShabat
