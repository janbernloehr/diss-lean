import NLS.KdV.HminusOneCharacteristicOrder
import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillMiuraTraceOrder
import NLS.KdV.MiuraCanonicalEndpoints
import NLS.ZakharovShabat.PeriodicEndpointMultiplicity
import NLS.SequenceSpaces.CoefficientDecay

/-!
# Actual high-pair transport through a rough real Miura lift

The fixed Dirac canonical endpoints are squared and translated at the same
index. Original physical algebraic multiplicities retain collapsed pairs.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

/-- A literal shifted real Miura representation identifies actual full-domain
physical multiplicities at every nonzero frequency. The shift may be complex. -/
theorem singularHillAlgebraicMultiplicity_shifted_miura (q : PeriodOneHminusOne)
    (u : PeriodOneRealL2) (c z : ℂ) (hz : z ≠ 0)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    singularHillAlgebraicMultiplicity (periodOneOriginal q) (z^2-c) =
      periodicAlgebraicMultiplicity (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) z := by
  have hpot : singularHillMiuraPotential (Coeff.periodDouble u.val) =
      periodOneOriginal q+l2OriginalHminus (lp.single 2 0 c) := by
    exact (singularHillMiuraPotential_periodDouble u.val).trans
      ((congrArg periodOneOriginal himage).trans (periodOneOriginal_add_constant q c))
  have hs := singularHillAlgebraicMultiplicity_add_constant (periodOneOriginal q) c (z^2-c)
  rw [sub_add_cancel,← hpot,singularHillAlgebraicMultiplicity_miura_dirac
    (Coeff.periodDouble u.val) (periodDouble_realType_diagonal u) z hz] at hs
  rw [periodOnePotential_apply,hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]
  exact hs.symm


/-- Two ordered roots in an actual real high pair exhaust its two slots
if a repeated candidate is counted at least twice. -/
theorem HillHminusRealHighPair.eq_of_ordered_roots
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} (p : HillHminusRealHighPair q n r)
    (a b : ℝ) (hab : a ≤ b)
    (ha : (a : ℂ) ∈ hillHminusGapSquareDisc n r)
    (hb : (b : ℂ) ∈ hillHminusGapSquareDisc n r)
    (hza : hillHminusRadicand q a = 0) (hzb : hillHminusRadicand q b = 0)
    (hm : a = b → 2 ≤ analyticOrderNatAt (hillHminusRadicand q) a) :
    a = p.left ∧ b = p.right := by
  have ha' : a = p.left ∨ a = p.right :=
    by simpa only [Complex.ofReal_inj] using (p.pair.zeros_iff a ha).mp hza
  have hb' : b = p.left ∨ b = p.right :=
    by simpa only [Complex.ofReal_inj] using (p.pair.zeros_iff b hb).mp hzb
  have hc : a = b → p.left = p.right := by
    intro he
    have hh := hm he
    rw [p.pair.multiplicity a ha] at hh
    by_contra hne
    rcases ha' with he | he <;>
      simp [Complex.ofReal_inj,he,hne,eq_comm] at hh
  rcases ha' with ha' | ha'
  · rcases hb' with hb' | hb'
    · exact ⟨ha',hb'.trans (hc (ha'.trans hb'.symm))⟩
    · exact ⟨ha',hb'⟩
  · rcases hb' with hb' | hb'
    · have he : p.left = p.right := le_antisymm p.ordered (by linarith)
      exact ⟨ha'.trans he.symm,hb'.trans he⟩
    · have he := hc (ha'.trans hb'.symm)
      exact ⟨ha'.trans he.symm,hb'⟩

theorem hillMiuraDiracPair_real (u : PeriodOneRealL2) (n : ℤ) :
    (hillMiuraDiracLeft u.val n).im = 0 ∧ (hillMiuraDiracRight u.val n).im = 0 := by
  apply canonicalPeriodicEndpoints_im_eq_zero_of_realType (by norm_num) (by norm_num)
  exact isRealType_periodOnePotential _ (isRealType_hillMiuraDiagonal u)

theorem hillMiuraDiracPair_ordered (u : Coeff 2) (n : ℤ) :
    (hillMiuraDiracLeft u n).re ≤ (hillMiuraDiracRight u n).re :=
  NLS.ComplexAnalysis.re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _)).2.1 n)

/-- Positive canonical Dirac endpoints localized in a given Hill high disc
are the two actual Hill endpoints in the same index, including collapse. -/
theorem hillHminus_pair_eq_squared_miuraDirac
    (q : PeriodOneHminusOne) (_hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (n : ℕ+) (r : ℝ) (p : HillHminusRealHighPair q n r)
    (hpos : 0 < (hillMiuraDiracLeft u.val (n:ℕ)).re)
    (hleft : (((hillMiuraDiracLeft u.val (n:ℕ)).re^2-c : ℝ) : ℂ) ∈ hillHminusGapSquareDisc n r)
    (hright : (((hillMiuraDiracRight u.val (n:ℕ)).re^2-c : ℝ) : ℂ) ∈ hillHminusGapSquareDisc n r) :
    p.left = (hillMiuraDiracLeft u.val (n:ℕ)).re^2-c ∧
      p.right = (hillMiuraDiracRight u.val (n:ℕ)).re^2-c := by
  let a := (hillMiuraDiracLeft u.val (n:ℕ)).re
  let b := (hillMiuraDiracRight u.val (n:ℕ)).re
  have hab : a ≤ b := hillMiuraDiracPair_ordered u.val _
  have hbpos : 0 < b := hpos.trans_le hab
  have hreal := hillMiuraDiracPair_real u (n:ℕ)
  have haC : (a : ℂ) = hillMiuraDiracLeft u.val (n:ℕ) := by
    apply Complex.ext <;> simp [a,hreal.1]
  have hbC : (b : ℂ) = hillMiuraDiracRight u.val (n:ℕ) := by
    apply Complex.ext <;> simp [b,hreal.2]
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by norm_num) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) (n:ℕ)
  have hroots (z : ℂ) (hz : z ∈ periodicSpectrum (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val))) : hillHminusRadicand q (z^2-(c:ℂ)) = 0 := by
    change hillHminusDiscriminant q (z^2-(c:ℂ)) ^ 2-4 = 0
    rw [hillHminusDiscriminant_shifted_miura_square q u.val (c:ℂ) z himage]
    exact sub_eq_zero.mpr ((canonicalDiscriminant_sq_eq_four_iff_finite
      (by norm_num) (by norm_num) _ (periodOnePotential_mem _) z).mpr hz)
  have hza : hillHminusRadicand q (((a^2-c : ℝ) : ℂ)) = 0 := by
    simpa only [ofReal_sub,ofReal_pow,haC,hillMiuraDiracLeft] using hroots _ hs.1
  have hzb : hillHminusRadicand q (((b^2-c : ℝ) : ℂ)) = 0 := by
    simpa only [ofReal_sub,ofReal_pow,hbC,hillMiuraDiracRight] using hroots _ hs.2
  have hm : a^2-c = b^2-c → 2 ≤ analyticOrderNatAt (hillHminusRadicand q) (((a^2-c : ℝ) : ℂ)) := by
    intro he
    have hab' : a = b := by nlinarith
    have he' : hillMiuraDiracLeft u.val (n:ℕ) = hillMiuraDiracRight u.val (n:ℕ) := by
      rw [← haC,← hbC,hab']
    have hmul := (canonicalPeriodicEndpoints_spec (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)).1.multiplicity_ge_two_of_eq
        (n:ℕ) he'
    rw [ofReal_sub,ofReal_pow,analyticOrderNatAt_hillHminusRadicand_shifted_miura q u.val (c:ℂ) (a:ℂ)
        (by exact_mod_cast ne_of_gt hpos) himage,haC]
    simpa only [hillMiuraDiracLeft] using hmul
  have he := p.eq_of_ordered_roots (a^2-c) (b^2-c) (by nlinarith)
    hleft hright hza hzb hm
  exact ⟨he.1.symm,he.2.symm⟩

/-- A small frequency displacement remains in the corresponding energy
disc after a fixed translation. The margin absorbs the fixed constant. -/
theorem abs_miura_square_translation_lt (t r c a : ℝ) (ht : 0 < t) (hr : 0 < r)
    (hc : 1+|c| ≤ t*r/4) (ha : |a-t| < min 1 (r/8)) :
    |a^2-c-t^2| < t*r := by
  have ha1 : |a-t| < 1 := ha.trans_le (min_le_left _ _)
  have har : |a-t| < r/8 := ha.trans_le (min_le_right _ _)
  have hd : (a-t)^2 < 1 := by
    have hh := mul_pos (show 0 < 1-(a-t) by linarith [(abs_lt.mp ha1).2])
      (show 0 < 1+(a-t) by linarith [(abs_lt.mp ha1).1])
    nlinarith
  have hterm : |2*t*(a-t)| < t*r/4 := by
    rw [abs_mul,abs_of_pos (show 0 < 2*t by linarith)]
    have hh := mul_lt_mul_of_pos_left har (show 0 < 2*t by linarith)
    nlinarith
  have hbound : |a^2-c-t^2| ≤ (a-t)^2+|2*t*(a-t)|+|c| := by
    calc
      _ = |(a-t)^2+2*t*(a-t)+(-c)| := by congr 1; ring
      _ ≤ |(a-t)^2+2*t*(a-t)|+|-c| := abs_add_le _ _
      _ ≤ (|(a-t)^2|+|2*t*(a-t)|)+|-c| := by
        linarith [abs_add_le ((a-t)^2) (2*t*(a-t))]
      _ = _ := by rw [abs_of_nonneg (sq_nonneg _),abs_neg]
  nlinarith [mul_pos ht hr]

/-- For any fixed positive radius and real translation, the actual positive
Dirac tail is positive and its squared translated endpoints lie in the
Hill disc with the SAME unsigned index. -/
theorem exists_miuraDirac_high_square_localization
    (u : PeriodOneRealL2) (c r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 < (hillMiuraDiracLeft u.val n).re ∧
      Real.pi*(n:ℝ) ≤ (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re ∧
      (((hillMiuraDiracLeft u.val n).re^2-c : ℝ) : ℂ) ∈
        ball (((Real.pi:ℂ)*n)^2) (Real.pi*(n:ℝ)*r) ∧
      (((hillMiuraDiracRight u.val n).re^2-c : ℝ) : ℂ) ∈
        ball (((Real.pi:ℂ)*n)^2) (Real.pi*(n:ℝ)*r) := by
  let δ := min 1 (r/8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨L,hL⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) hδ
  obtain ⟨R,hR⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicRightDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) hδ
  obtain ⟨K,hK⟩ := exists_nat_gt (4*(1+|c|)/(Real.pi*r))
  refine ⟨max 2 (max L (max R K)),le_max_left _ _,fun n hn => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnL : L ≤ n := by omega
  have hnR : R ≤ n := by omega
  have hnK : K ≤ n := by omega
  have hnormL : ‖hillMiuraDiracLeft u.val n-(Real.pi:ℂ)*n‖ < δ := by
    simpa only [canonicalPeriodicLeftDisplacement_apply,hillMiuraDiracLeft,Int.cast_natCast] using
      hL (n:ℤ) (by simpa using hnL)
  have hnormR : ‖hillMiuraDiracRight u.val n-(Real.pi:ℂ)*n‖ < δ := by
    simpa only [canonicalPeriodicRightDisplacement_apply,hillMiuraDiracRight,Int.cast_natCast] using
      hR (n:ℤ) (by simpa using hnR)
  have habsL : |(hillMiuraDiracLeft u.val n).re-Real.pi*(n:ℝ)| < δ := by
    have hh := (Complex.abs_re_le_norm (hillMiuraDiracLeft u.val n-(Real.pi:ℂ)*n)).trans_lt hnormL
    simpa only [sub_re,mul_re,ofReal_re,natCast_re,ofReal_im,natCast_im,mul_zero,sub_zero] using hh
  have habsR : |(hillMiuraDiracRight u.val n).re-Real.pi*(n:ℝ)| < δ := by
    have hh := (Complex.abs_re_le_norm (hillMiuraDiracRight u.val n-(Real.pi:ℂ)*n)).trans_lt hnormR
    simpa only [sub_re,mul_re,ofReal_re,natCast_re,ofReal_im,natCast_im,mul_zero,sub_zero] using hh
  have hmargin : 1+|c| ≤ Real.pi*(n:ℝ)*r/4 := by
    have hk := (div_lt_iff₀ (mul_pos Real.pi_pos hr)).mp hK
    have hkn : (K:ℝ) ≤ n := by exact_mod_cast hnK
    have hh := mul_le_mul_of_nonneg_right hkn (mul_pos Real.pi_pos hr).le
    nlinarith
  have hnp : 0 < Real.pi*(n:ℝ) := mul_pos Real.pi_pos (by positivity)
  have hfree : 2 < Real.pi*(n:ℝ) := by
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hh := mul_le_mul_of_nonneg_left hnr Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have hL1 := habsL.trans_le (min_le_left 1 (r/8))
  have hR1 := habsR.trans_le (min_le_left 1 (r/8))
  refine ⟨by linarith [(abs_lt.mp hL1).1],by linarith [(abs_lt.mp hL1).1,(abs_lt.mp hR1).1],?_,?_⟩
  · rw [mem_ball,dist_eq_norm]
    have he : (((hillMiuraDiracLeft u.val n).re^2-c : ℝ) : ℂ)-((Real.pi:ℂ)*n)^2 =
        (((hillMiuraDiracLeft u.val n).re^2-c-(Real.pi*(n:ℝ))^2 : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact abs_miura_square_translation_lt _ r c _ hnp hr hmargin habsL
  · rw [mem_ball,dist_eq_norm]
    have he : (((hillMiuraDiracRight u.val n).re^2-c : ℝ) : ℂ)-((Real.pi:ℂ)*n)^2 =
        (((hillMiuraDiracRight u.val n).re^2-c-(Real.pi*(n:ℝ))^2 : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact abs_miura_square_translation_lt _ r c _ hnp hr hmargin habsR

/-- Every sufficiently high intrinsic Hill slot is the square-minus-shift
of the actual canonical Dirac slot at the SAME index. The cutoff is proved,
and collapsed pairs remain included. -/
theorem exists_hillHminusLabels_squared_miuraDirac
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      hillHminusLabels q hq (2*n-1) = (hillMiuraDiracLeft u.val n).re^2-c ∧
      hillHminusLabels q hq (2*n) = (hillMiuraDiracRight u.val n).re^2-c ∧
      Real.pi*(n:ℝ) ≤ (hillMiuraDiracLeft u.val n).re+(hillMiuraDiracRight u.val n).re := by
  obtain ⟨M,r,hlabels⟩ := hillHminusLabels_spec q hq
  obtain ⟨K,hK,hlocal⟩ := exists_miuraDirac_high_square_localization u c r hlabels.radius_pos
  refine ⟨max M K,hK.trans (le_max_right _ _),fun n hn => ?_⟩
  have hnM : M ≤ n := (le_max_left _ _).trans hn
  have hnK : K ≤ n := (le_max_right _ _).trans hn
  obtain ⟨p,hl,hr⟩ := hlabels.high_pair n hnM
  obtain ⟨hpos,hsum,hleft,hright⟩ := hlocal n hnK
  have he := hillHminus_pair_eq_squared_miuraDirac q hq u c himage
    ⟨n,by have := hlabels.cutoff_ge_two; omega⟩ r p hpos
    (ball_subset_closedBall hleft) (ball_subset_closedBall hright)
  exact ⟨hl.trans he.1,hr.trans he.2,hsum⟩

/-- The norm form of pair transport also works at negative Dirac indices.
The squared candidates can exchange order; their gap norm is unchanged. -/
theorem hillHminus_pair_gap_norm_eq_miuraDirac
    (q : PeriodOneHminusOne) (_hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (k : ℤ) (n : ℕ+) (r : ℝ) (p : HillHminusRealHighPair q n r)
    (hleftNe : hillMiuraDiracLeft u.val k ≠ 0)
    (hsumNe : hillMiuraDiracLeft u.val k+hillMiuraDiracRight u.val k ≠ 0)
    (hleft : (((hillMiuraDiracLeft u.val k).re^2-c : ℝ) : ℂ) ∈ hillHminusGapSquareDisc n r)
    (hright : (((hillMiuraDiracRight u.val k).re^2-c : ℝ) : ℂ) ∈ hillHminusGapSquareDisc n r) :
    ‖((p.right-p.left : ℝ) : ℂ)‖ =
      ‖hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k‖*
        ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ := by
  let a := (hillMiuraDiracLeft u.val k).re
  let b := (hillMiuraDiracRight u.val k).re
  have hreal := hillMiuraDiracPair_real u k
  have haC : (a:ℂ) = hillMiuraDiracLeft u.val k := by apply Complex.ext <;> simp [a,hreal.1]
  have hbC : (b:ℂ) = hillMiuraDiracRight u.val k := by apply Complex.ext <;> simp [b,hreal.2]
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by norm_num) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) k
  have hroots (z : ℂ) (hz : z ∈ periodicSpectrum (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val))) : hillHminusRadicand q (z^2-(c:ℂ)) = 0 := by
    change hillHminusDiscriminant q (z^2-(c:ℂ)) ^ 2-4 = 0
    rw [hillHminusDiscriminant_shifted_miura_square q u.val (c:ℂ) z himage]
    exact sub_eq_zero.mpr ((canonicalDiscriminant_sq_eq_four_iff_finite
      (by norm_num) (by norm_num) _ (periodOnePotential_mem _) z).mpr hz)
  have hza : hillHminusRadicand q (((a^2-c : ℝ) : ℂ)) = 0 := by
    simpa only [ofReal_sub,ofReal_pow,haC,hillMiuraDiracLeft] using hroots _ hs.1
  have hzb : hillHminusRadicand q (((b^2-c : ℝ) : ℂ)) = 0 := by
    simpa only [ofReal_sub,ofReal_pow,hbC,hillMiuraDiracRight] using hroots _ hs.2
  have hm : a^2-c = b^2-c → 2 ≤ analyticOrderNatAt (hillHminusRadicand q) (((a^2-c : ℝ) : ℂ)) := by
    intro he
    have hab : a+b ≠ 0 := by
      intro hh
      apply hsumNe
      rw [← haC,← hbC,← ofReal_add,hh,ofReal_zero]
    have hab' : a = b := sub_eq_zero.mp ((mul_eq_zero.mp
      (show (a-b)*(a+b) = 0 by nlinarith)).resolve_right hab)
    have he' : hillMiuraDiracLeft u.val k = hillMiuraDiracRight u.val k := by rw [← haC,← hbC,hab']
    have hmul := (canonicalPeriodicEndpoints_spec (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)).1.multiplicity_ge_two_of_eq k he'
    rw [ofReal_sub,ofReal_pow,analyticOrderNatAt_hillHminusRadicand_shifted_miura q u.val (c:ℂ) (a:ℂ)
        (by rwa [haC]) himage,haC]
    simpa only [hillMiuraDiracLeft] using hmul
  have hc : (((b^2-a^2 : ℝ) : ℂ)) =
      (hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k)*
        (hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k) := by
    rw [← haC,← hbC]
    push_cast
    ring
  by_cases horder : a^2-c ≤ b^2-c
  · obtain ⟨ha,hb⟩ := p.eq_of_ordered_roots (a^2-c) (b^2-c) horder hleft hright hza hzb hm
    have he : p.right-p.left = b^2-a^2 := by rw [← ha,← hb]; ring
    rw [he,hc,norm_mul]
  · obtain ⟨hb,ha⟩ := p.eq_of_ordered_roots (b^2-c) (a^2-c) (le_of_not_ge horder)
      hright hleft hzb hza (fun he => by rw [he]; exact hm he.symm)
    have he : p.right-p.left = -(b^2-a^2) := by rw [← ha,← hb]; ring
    rw [he,ofReal_neg,norm_neg,hc,norm_mul]

/-- Two-sided localization at the unsigned Hill index. No reflection law
for the canonical Dirac labels is assumed. -/
theorem exists_miuraDirac_signed_square_localization
    (u : PeriodOneRealL2) (c r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℤ, N ≤ k.natAbs →
      hillMiuraDiracLeft u.val k ≠ 0 ∧
      Real.pi*(k.natAbs:ℝ) ≤ ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ ∧
      (((hillMiuraDiracLeft u.val k).re^2-c : ℝ) : ℂ) ∈
        ball (((Real.pi:ℂ)*k.natAbs)^2) (Real.pi*(k.natAbs:ℝ)*r) ∧
      (((hillMiuraDiracRight u.val k).re^2-c : ℝ) : ℂ) ∈
        ball (((Real.pi:ℂ)*k.natAbs)^2) (Real.pi*(k.natAbs:ℝ)*r) := by
  let δ := min 1 (r/8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨L,hL⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) hδ
  obtain ⟨R,hR⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num)
    (canonicalPeriodicRightDisplacement (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)) hδ
  obtain ⟨K,hK⟩ := exists_nat_gt (4*(1+|c|)/(Real.pi*r))
  refine ⟨max 2 (max L (max R K)),le_max_left _ _,fun k hk => ?_⟩
  have hk2 : 2 ≤ k.natAbs := (le_max_left _ _).trans hk
  have hkL : L ≤ k.natAbs := by omega
  have hkR : R ≤ k.natAbs := by omega
  have hkK : K ≤ k.natAbs := by omega
  have hnormL : ‖hillMiuraDiracLeft u.val k-(Real.pi:ℂ)*k‖ < δ := hL k hkL
  have hnormR : ‖hillMiuraDiracRight u.val k-(Real.pi:ℂ)*k‖ < δ := hR k hkR
  have ht : 2 < Real.pi*(k.natAbs:ℝ) := by
    have hnr : (1:ℝ) ≤ k.natAbs := by exact_mod_cast (show 1 ≤ k.natAbs by omega)
    have hh := mul_le_mul_of_nonneg_left hnr Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have hf : ‖(Real.pi:ℂ)*k‖ = Real.pi*(k.natAbs:ℝ) := by
    have he : (Real.pi:ℂ)*k = ((Real.pi*(k:ℝ):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,
      Nat.cast_natAbs,Int.cast_abs]
  have hL1 : ‖hillMiuraDiracLeft u.val k-(Real.pi:ℂ)*k‖ < 1 := hnormL.trans_le (min_le_left _ _)
  have hR1 : ‖hillMiuraDiracRight u.val k-(Real.pi:ℂ)*k‖ < 1 := hnormR.trans_le (min_le_left _ _)
  have hsumNorm : Real.pi*(k.natAbs:ℝ) ≤ ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ := by
    have he : ‖(hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k)-2*((Real.pi:ℂ)*k)‖ < 2 := by
      have heq : (hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k)-2*((Real.pi:ℂ)*k) =
          (hillMiuraDiracRight u.val k-(Real.pi:ℂ)*k)+(hillMiuraDiracLeft u.val k-(Real.pi:ℂ)*k) := by ring
      rw [heq]
      exact (norm_add_le _ _).trans_lt (by linarith)
    have hh := norm_le_norm_sub_add (2*((Real.pi:ℂ)*k))
      (hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k)
    rw [norm_mul,norm_ofNat,hf,norm_sub_rev] at hh
    nlinarith
  have hmargin : 1+|c| ≤ Real.pi*(k.natAbs:ℝ)*r/4 := by
    have hh := (div_lt_iff₀ (mul_pos Real.pi_pos hr)).mp hK
    have hkn : (K:ℝ) ≤ k.natAbs := by exact_mod_cast hkK
    have hb := mul_le_mul_of_nonneg_right hkn (mul_pos Real.pi_pos hr).le
    nlinarith
  have habs (z : ℂ) (hz : ‖z-(Real.pi:ℂ)*k‖ < δ) :
      abs (abs z.re-Real.pi*(k.natAbs:ℝ)) < δ := by
    have hh := (Complex.abs_re_le_norm (z-(Real.pi:ℂ)*k)).trans_lt hz
    have hh' : |z.re-Real.pi*(k:ℝ)| < δ := by
      simpa only [sub_re,mul_re,ofReal_re,intCast_re,ofReal_im,intCast_im,mul_zero,sub_zero] using hh
    have hb := (abs_abs_sub_abs_le_abs_sub z.re (Real.pi*(k:ℝ))).trans_lt hh'
    simpa only [abs_mul,abs_of_pos Real.pi_pos,Nat.cast_natAbs,Int.cast_abs] using hb
  have hlocal (z : ℂ) (hz : ‖z-(Real.pi:ℂ)*k‖ < δ) :
      (((z.re^2-c : ℝ):ℂ)) ∈ ball (((Real.pi:ℂ)*k.natAbs)^2) (Real.pi*(k.natAbs:ℝ)*r) := by
    rw [mem_ball,dist_eq_norm]
    have he : (((z.re^2-c : ℝ):ℂ))-((Real.pi:ℂ)*k.natAbs)^2 =
        ((z.re^2-c-(Real.pi*(k.natAbs:ℝ))^2:ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    simpa only [sq_abs] using abs_miura_square_translation_lt
      (Real.pi*(k.natAbs:ℝ)) r c |z.re| (by linarith) hr hmargin (habs z hz)
  refine ⟨?_,hsumNorm,hlocal _ hnormL,hlocal _ hnormR⟩
  intro hzero
  rw [hzero,zero_sub,norm_neg,hf] at hL1
  linarith

end NLS.KdV
