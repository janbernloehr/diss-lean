import NLS.KdV.HminusOneDirichletHighGaps

/-! Unique scalar Dirichlet zeros in the intrinsic original high gaps.
Actual auxiliary spectral isolation supplies uniqueness, while the real
square root preserves the positive high-gap order. -/
noncomputable section
open Set Complex Metric NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- One common cutoff isolates every distant canonical diagonal auxiliary
Dirichlet root as the only characteristic zero in its original free disc. -/
theorem exists_hillMiuraDiracDirichlet_unique_tail (u : Coeff 2) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ,
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u) z = 0 → z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4) →
      z = hillMiuraDiracDirichlet u n := by
  let P := auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num) (hillMiuraDiagonal u)
  let K := BoundaryCondition.canonicalRootCutoff .dirichlet (by simp) (by norm_num) P.val P.property
  have hs := (BoundaryCondition.canonicalRoots_spec .dirichlet (by simp) (by norm_num)
    P.val P.property).1
  refine ⟨max 2 (K+1),le_max_left _ _,fun n hn z hz hd => ?_⟩
  have hnK : K < n.natAbs := by have := (le_max_right 2 (K+1)).trans hn; omega
  have hz' : z ∈ BoundaryCondition.spectrum .dirichlet (by simp) P.val P.property :=
    (BoundaryCondition.characteristic_eq_zero_iff .dirichlet (by simp) (by norm_num)
      P.val P.property z).mp hz
  have hm := (BoundaryCondition.mem_enclosedSpectrum .dirichlet (by simp)
    P.val P.property ((Real.pi:ℂ)*n) z (Real.pi/4)).mpr ⟨hz',hd⟩
  rw [(hs.counting.eigenvalue_spec .dirichlet n hnK).1] at hm
  exact (Finset.mem_singleton.mp hm).trans (hs.distant n hnK).symm

/-- The entire real interval between the two positive high periodic
Dirac endpoints lies in the same original auxiliary isolating disc. -/
theorem exists_hillMiuraDirac_interval_in_disc (u : PeriodOneRealL2) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 < (hillMiuraDiracLeft u.val n).re ∧ ∀ t : ℝ,
        (hillMiuraDiracLeft u.val n).re ≤ t → t ≤ (hillMiuraDiracRight u.val n).re →
        (t:ℂ) ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4) := by
  have heps : 0 < Real.pi/8 := by positivity
  obtain ⟨L,hL⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicLeftDisplacement (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) heps
  obtain ⟨R,hR⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicRightDisplacement (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) heps
  refine ⟨max 2 (max L R),le_max_left _ _,fun n hn => ?_⟩
  have hnL : L ≤ n := by omega
  have hnR : R ≤ n := by omega
  have hleft : |(hillMiuraDiracLeft u.val n).re-Real.pi*(n:ℝ)| < Real.pi/8 := by
    have h := (Complex.abs_re_le_norm
      (hillMiuraDiracLeft u.val n-(Real.pi:ℂ)*n)).trans_lt (hL n (by simpa using hnL))
    simpa only [canonicalPeriodicLeftDisplacement_apply,hillMiuraDiracLeft,
      Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.natCast_re,
      Complex.ofReal_im,Complex.natCast_im,mul_zero,sub_zero] using h
  have hright : |(hillMiuraDiracRight u.val n).re-Real.pi*(n:ℝ)| < Real.pi/8 := by
    have h := (Complex.abs_re_le_norm
      (hillMiuraDiracRight u.val n-(Real.pi:ℂ)*n)).trans_lt (hR n (by simpa using hnR))
    simpa only [canonicalPeriodicRightDisplacement_apply,hillMiuraDiracRight,
      Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.natCast_re,
      Complex.ofReal_im,Complex.natCast_im,mul_zero,sub_zero] using h
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp := mul_le_mul_of_nonneg_left hnr Real.pi_pos.le
  refine ⟨by nlinarith [(abs_lt.mp hleft).1,Real.pi_pos],fun t htL htR => ?_⟩
  rw [mem_ball,dist_eq_norm]
  have he : (t:ℂ)-(Real.pi:ℂ)*n = ((t-Real.pi*(n:ℝ):ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hleft).1,Real.pi_pos],
    by linarith [(abs_lt.mp hright).2,Real.pi_pos]⟩

/-- Every sufficiently high intrinsic original real Hill gap contains
EXACTLY ONE scalar Dirichlet zero, including a collapsed periodic pair.
The assertion is intrinsic to q; no selected Miura branch occurs in it. -/
theorem exists_unique_hillHminusDirichlet_zero_in_high_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃! x : ℝ,
      hillHminusDirichlet q x = 0 ∧
        x ∈ Icc (hillHminusLabels q hq (2*n-1)) (hillHminusLabels q hq (2*n)) := by
  obtain ⟨L,hL,hgap⟩ := exists_hillMiuraDirichletEnergy_in_high_gap q hq u c hi
  obtain ⟨K,_,hlabels⟩ := exists_hillHminusLabels_squared_miuraDirac q hq u c hi
  obtain ⟨M,_,hdisc⟩ := exists_hillMiuraDirac_interval_in_disc u
  obtain ⟨J,_,hunique⟩ := exists_hillMiuraDiracDirichlet_unique_tail u.val
  refine ⟨max L (max K (max M J)),hL.trans (le_max_left _ _),fun n hn => ?_⟩
  have hnL : L ≤ n := by omega
  have hnK : K ≤ n := by omega
  have hnM : M ≤ n := by omega
  have hnJ : J ≤ n := by omega
  obtain ⟨hz,_,hlo,hhi,_⟩ := hgap n hnL
  have hrE := hillHminusDirichlet_im_eq_zero_of_real q hq _ hz
  have he : ((hillMiuraDirichletEnergy u.val c n).re:ℂ) = hillMiuraDirichletEnergy u.val c n := by
    apply Complex.ext <;> simp [hrE]
  refine ⟨(hillMiuraDirichletEnergy u.val c n).re,⟨by rwa [he],hlo,hhi⟩,?_⟩
  rintro x ⟨hx,hxlo,hxhi⟩
  obtain ⟨hl,hr,_⟩ := hlabels n hnK
  obtain ⟨ha,hinterval⟩ := hdisc n hnM
  rw [hl] at hxlo
  rw [hr] at hxhi
  let t := Real.sqrt (x+c)
  have hxc : 0 ≤ x+c := by nlinarith [sq_nonneg (hillMiuraDiracLeft u.val n).re]
  have hsq : t^2 = x+c := Real.sq_sqrt hxc
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htL : (hillMiuraDiracLeft u.val n).re ≤ t := by nlinarith
  have hb := hillMiuraDiracPair_ordered u.val n
  have htR : t ≤ (hillMiuraDiracRight u.val n).re := by nlinarith
  have hsqC : (t:ℂ)^2 = (x:ℂ)+(c:ℂ) := by exact_mod_cast hsq
  have hzero : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u.val) t = 0 := by
    rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u.val (c:ℂ) t hi,
      hsqC,add_sub_cancel_right,hx,mul_zero]
  have ht := hunique n (by simpa using hnJ) t hzero (hinterval t htL htR)
  have hre : t = (hillMiuraDiracDirichlet u.val n).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re ht
  have hreal := hillMiuraDiracDirichlet_im_eq_zero u n
  change x = ((hillMiuraDiracDirichlet u.val n)^2-(c:ℂ)).re
  simp only [pow_two,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,hreal,mul_zero,sub_zero]
  nlinarith

/-- The intrinsic high-gap uniqueness statement holds for EVERY real
original H-minus-one potential: a literal real Miura lift is constructed
inside the proof, rather than left as a hypothesis. -/
theorem exists_unique_hillHminusDirichlet_zero_in_high_gap_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃! x : ℝ,
      hillHminusDirichlet q x = 0 ∧
        x ∈ Icc (hillHminusLabels q hq (2*n-1)) (hillHminusLabels q hq (2*n)) := by
  obtain ⟨c,_,_,u,hi⟩ := exists_real_periodOneMiura_shift q hq 0
  exact exists_unique_hillHminusDirichlet_zero_in_high_gap q hq u (c^2)
    (by simpa only [Complex.ofReal_pow] using hi)

end NLS.KdV
