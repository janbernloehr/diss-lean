import NLS.KdV.HillHminusOneDirichletLogNorming
import NLS.KdV.HillHminusOneRealGapProfile

/-! # Actual Dirichlet logarithmic norming data and the canonical gap profile

The original endpoint multiplier gives the exact cosh trace identity.
Consequently the absolute logarithmic norming coordinate is the already
constructed source-normalized arcosh gap profile at the actual Dirichlet
label. Its zero set is precisely the two gap endpoints, including the
collapsed-gap case. No Birkhoff coordinate identity is substituted.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

theorem hillHminusDirichletLogNorming_cosh_trace (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (-1 : ℝ)^(n : ℕ)*(hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)).re =
      2*Real.cosh (hillHminusDirichletLogNorming q hr n) := by
  let w := hillHminusDirichletNorming q hr n
  let D := (hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)).re
  let s : ℝ := (-1)^(n : ℕ)
  let f := s*w.re
  have hs : s^2 = 1 := by dsimp [s]; rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]; norm_num
  have hw : w.im = 0 := hillHminusDirichletNorming_real q hr n
  have h := congrArg Complex.re (hillHminusDirichletNorming_characteristic q hr n)
  change (w^2-hillHminusDiscriminant q (hillHminusDirichletEnergy q hr n)*w+1).re = 0 at h
  have hquad : w.re^2-D*w.re+1 = 0 := by
    simpa only [pow_two,mul_re,sub_re,add_re,hw,mul_zero,zero_mul,sub_zero,one_re,zero_re,D] using h
  have hf : f ≠ 0 := (hillHminusDirichletNorming_signed_pos q hr n).ne'
  have hid : (s*D)*f = f^2+1 := by
    change (s*D)*(s*w.re) = (s*w.re)^2+1
    calc
      _ = s^2*(D*w.re) := by ring
      _ = (s*w.re)^2+1 := by rw [hs,one_mul,mul_pow,hs,one_mul]; linarith [hquad]
  have htrace : s*D = f+f⁻¹ := by
    apply mul_right_cancel₀ hf
    rw [hid,add_mul,inv_mul_cancel₀ hf]
    ring
  have he : Real.exp (hillHminusDirichletLogNorming q hr n) = f := exp_hillHminusDirichletLogNorming q hr n
  change s*D = _
  rw [Real.cosh_eq,Real.exp_neg,he]
  linarith [htrace]

theorem hillHminusRealGapProfile_dirichlet_eq_abs_logNorming
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapProfile q (n : ℕ) (hillHminusDirichletEnergy q hr n) =
      |hillHminusDirichletLogNorming q hr n| := by
  rw [hillHminusRealGapProfile,hillHminusDirichletLogNorming_cosh_trace]
  rw [show (2*Real.cosh (hillHminusDirichletLogNorming q hr n))/2 =
    Real.cosh (hillHminusDirichletLogNorming q hr n) by ring]
  rw [← Real.cosh_abs (hillHminusDirichletLogNorming q hr n)]
  exact Real.arcosh_cosh (abs_nonneg _)

theorem hillHminusDirichletLogNorming_eq_zero_iff_endpoint
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichletLogNorming q hr n = 0 ↔
      hillHminusDirichletEnergy q hr n = hillHminusRealLabels q hr (2*(n : ℕ)-1) ∨
      hillHminusDirichletEnergy q hr n = hillHminusRealLabels q hr (2*(n : ℕ)) := by
  have hm := hillHminusDirichletEnergy_mem_gap q hr n
  have he := hillHminusRealGapProfile_dirichlet_eq_abs_logNorming q hr n
  constructor
  · intro hz
    by_contra hnot
    push Not at hnot
    have hp := hillHminusRealGapProfile_pos q hr (n : ℕ) n.property _
      ⟨lt_of_le_of_ne hm.1 (Ne.symm hnot.1),lt_of_le_of_ne hm.2 hnot.2⟩
    rw [he,hz,abs_zero] at hp
    exact lt_irrefl _ hp
  · intro hend
    have hz : hillHminusRealGapProfile q (n : ℕ) (hillHminusDirichletEnergy q hr n) = 0 := by
      rcases hend with h | h
      · rw [h]
        exact (hillHminusRealGapProfile_endpoints q hr (n : ℕ) n.property).1
      · rw [h]
        exact (hillHminusRealGapProfile_endpoints q hr (n : ℕ) n.property).2
    rw [he] at hz
    exact abs_eq_zero.mp hz

end NLS.KdV
