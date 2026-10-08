import NLS.ZakharovShabat.OrderedGapProductBound
import NLS.ZakharovShabat.SourceRealGapFactorBound
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder

/-! # A squared-norm bound for finite products of actual real-source gap factors -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real spectral point outside a finite enclosing interval controls the
actual critical-root product by a single ratio, after squaring its norm. -/
theorem sourceReal_finite_gap_product_sq_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (s : Finset ℤ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ m ∈ s,
      |(canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re| ≤ A ∧
      |(canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re| ≤ A)
    (z : ℂ) (hzim : z.im = 0) (hz : A < |z.re|) :
    ‖∏ m ∈ s, (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
      sourceStandardRoot hp hp1 ψ m z‖^2 ≤ (|z.re|+A)/(|z.re|-A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let c := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hreal' := isRealType_periodOnePotential ψ hreal
  have real_eq (u : ℂ) (hu : u.im = 0) : (u.re:ℂ) = u := by
    apply Complex.ext <;> simp [hu]
  have hl (m : ℤ) : ((l m).re:ℂ) = l m := real_eq _
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal' m).1
  have hr (m : ℤ) : ((r m).re:ℂ) = r m := real_eq _
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal' m).2
  have hc (m : ℤ) : ((c m).re:ℂ) = c m := real_eq _
    (canonicalCriticalPoints_im_eq_zero hp hp1 _ _ hreal' m)
  have hze := real_eq z hzim
  have h := ordered_real_gap_product_sq_le s (fun m => (l m).re) (fun m => (r m).re)
    (fun m => (c m).re) (fun m => sourceStandardRoot hp hp1 ψ m z) A z.re hA hz
    (fun m hm => by
      have hcrit := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) hreal' m
      exact ⟨(abs_le.mp (hb m hm).1).1,hcrit.1,hcrit.2,(abs_le.mp (hb m hm).2).2⟩)
    (fun i _ j _ hij => (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ _ hreal' hij).le)
    (fun m hm => by
      rw [hl,hr,hze]
      apply sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z
      intro hseg
      have hi := sourcePeriodicSegment_re_mem_Icc hp hp1 ψ m z hseg
      have hlo := (abs_le.mp (hb m hm).1).1
      have hhi := (abs_le.mp (hb m hm).2).2
      exact (not_le_of_gt hz) (abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩))
  simpa only [hc,hze] using h

end NLS.ZakharovShabat
