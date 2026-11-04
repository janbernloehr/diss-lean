import NLS.KdV.HillHminusOneRealContinuationBands
import NLS.KdV.HillHminusOneEnergyRootContinuationAgreement
import NLS.ZakharovShabat.RealGapProductSigns

/-! # Canonical roots on every original rough Hill contour

A negative real radicand excludes all canonical cuts. Real crossings and
nonreal points of the original circles therefore lie in the canonical
root domain. One actual chart and norm ball give equality of both roots
and their full complex germs before all real inputs and contour indices.
Actual period transfer between differently mapped loops remains open.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexOrder
namespace NLS.KdV

/-- A nonnegative energy in the original continued domain lies in every applicable positive real-shift canonical root domain. -/
theorem hillHminus_nonnegative_continuation_mem_energyRootDomain (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain)
    (hq : periodOneHminusConjugation q = q)
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (x : ℝ) (hx : 0 ≤ x) (hdom : ((x : ℂ),q) ∈ hillHminusContinuationDomain) :
    (x : ℂ) ∈ C.energyRootDomain q := by
  have hs : (x : ℂ)+C.energyShift = ((x+C.energyShift.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hc]
  have hz : sqrt ((x : ℂ)+C.energyShift) = ((Real.sqrt (x+C.energyShift.re) : ℝ) : ℂ) := by
    rw [hs,Complex.sqrt_of_nonneg (by exact_mod_cast (show 0 ≤ x+C.energyShift.re by linarith))]
    rfl
  refine ⟨Or.inl (by simp only [add_re,ofReal_re];linarith),?_⟩
  rw [hz]
  intro n hn
  have hI := sourcePeriodicSegment_re_mem_Icc (by simp) (by norm_num)
    (C.criticalSource q) n _ hn
  simp only [ofReal_re] at hI
  have hgap := discriminant_re_sq_ge_four_of_mem_canonicalGap (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ hr) n (Real.sqrt (x+C.energyShift.re)) hI
  have hneg := hillHminusRadicand_re_neg_of_real_continuation q hq x hx hdom
  have htrace := C.trace_shifted_square q hqC (sqrt ((x : ℂ)+C.energyShift))
  rw [sq_sqrt,add_sub_cancel_right,hz] at htrace
  have him := hillHminusDiscriminant_im_eq_zero_of_real_nonnegative q hq x hx
  simp only [hillHminusRadicand,sub_re,pow_two,mul_re,him,mul_zero,sub_zero] at hneg
  norm_num at hneg
  rw [← htrace] at hgap
  nlinarith

/-- Squared points in the right half-plane of the original continued domain belong to the canonical root domain. -/
theorem hillHminus_rightHalf_square_continuation_mem_energyRootDomain (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain)
    (hq : periodOneHminusConjugation q = q)
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (z : ℂ) (hz : 0 < z.re) (hdom : (z^2,q) ∈ hillHminusContinuationDomain) :
    z^2 ∈ C.energyRootDomain q := by
  by_cases hi : (z^2).im ≠ 0
  · exact C.nonreal_mem_energyRootDomain q hc hr _ hi
  have hi0 : (z^2).im = 0 := not_ne_iff.mp hi
  have hzim : z.im = 0 := by
    have he : (2*z.re)*z.im = 0 := by
      simp only [pow_two,mul_im] at hi0
      nlinarith
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  have he : z^2 = ((z.re^2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two,mul_re,mul_im,hzim]
  rw [he]
  exact hillHminus_nonnegative_continuation_mem_energyRootDomain C q hqC hq hcpos hc hr _
    (sq_nonneg _) (by rwa [← he])

/-- Every original positive frequency circle lies in the canonical energy-root domain at real rough inputs. -/
theorem hillHminus_original_contour_mem_energyRootDomain (C D : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} (E : HillHminusAllContourPeriodData D N V)
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (hqC : q ∈ C.domain)
    (hq : periodOneHminusConjugation q = q)
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (k : ℕ+) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    z^2 ∈ C.energyRootDomain q := by
  exact hillHminus_rightHalf_square_continuation_mem_energyRootDomain C q hqC hq hcpos hc hr z
    (re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz)) (E.cover k q hqV z hz)

/-- One norm ball precedes all real inputs and original contours: canonical and original continued roots agree there, together with their full complex germs. -/
theorem exists_hillHminus_original_contour_root_agreement (D : HillHminusMiuraChart)
    {N : ℕ} {U : Set PeriodOneHminusOne} (E : HillHminusAllContourPeriodData D N U) :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, 0 < δ ∧
      ball (0 : PeriodOneHminusOne) δ ⊆ U ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
        ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          z^2 ∈ C.energyRootDomain q ∧
          C.energyRoot q (z^2) = hillHminusContinuedRoot (z^2,q) ∧
          (fun t : ℂ × PeriodOneHminusOne => C.energyRoot t.2 t.1) =ᶠ[𝓝 (z^2,q)]
            hillHminusContinuedRoot := by
  obtain ⟨C,V,W₀,W,s,hV,h0,hVC,_,hpos,hc,hr,H,hVW,_,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks 0 periodOneHminusConjugation_zero
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hV.inter E.isOpen) 0 ⟨h0,E.zero_mem⟩
  refine ⟨C,δ,hδ,fun q hq => (hball hq).2,fun q hq => hVC (hball hq).1,?_⟩
  intro q hq hqReal k z hz
  have hqV := (hball hq).1
  have hrV : ∀ p ∈ V, periodOneHminusConjugation p = p →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource p)) := fun p hp hpr => (hr p (hVC hp) hpr).2
  have hpath (r : ℝ) (hrange : r ∈ Icc (0 : ℝ) 1) : (r : ℂ) • q ∈ V := by
    apply (fun hx => (hball hx).1)
    rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) hrange.2).trans_lt (mem_ball_zero_iff.mp hq)
  have hroot := hillHminus_original_contour_mem_energyRootDomain C D E q (hball hq).2
    (hVC hqV) hqReal hpos hc (hrV q hqV hqReal) k z hz
  have hcont := E.cover k q (hball hq).2 z hz
  exact ⟨hroot,C.energyRoot_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hrV q hqReal hpath
    ⟨hroot,hcont⟩,C.energyRoot_germ_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hrV q hqReal hpath
    (z^2) hroot hcont⟩

end NLS.KdV
