import NLS.KdV.HminusOneDirichletZeroEnergy

/-! Full positive-index enumeration of scalar Dirichlet zeros of real
original H-minus-one potentials through ANY literal real Miura lift.
The original central index is proved, not left as an eventual tail offset. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The squared real-profile auxiliary energy is a real scalar energy,
at every signed index and every real constant translation. -/
theorem hillMiuraDirichletEnergy_ofReal_re (u : PeriodOneRealL2) (c : ℝ) (n : ℤ) :
    ((hillMiuraDirichletEnergy u.val c n).re:ℂ) = hillMiuraDirichletEnergy u.val c n := by
  have hr := hillMiuraDiracDirichlet_im_eq_zero u n
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,hillMiuraDirichletEnergy,pow_two,Complex.sub_im,
      Complex.mul_im,hr,mul_zero,zero_mul,add_zero,sub_zero]

/-- The complete scalar Dirichlet zero set is the squared positive
canonical auxiliary sequence, including ALL central scalar energies. -/
theorem hillHminusDirichlet_roots_iff_positive_miura
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔ ∃ n : ℕ+,
      lambda = hillMiuraDirichletEnergy u.val c (n:ℕ) := by
  constructor
  · intro hl
    have hpos := hillHminusDirichlet_root_above_shift q u c hi lambda hl
    have hreal := hillHminusDirichlet_im_eq_zero_of_real q hq lambda hl
    have hval : (lambda.re:ℂ) = lambda := by apply Complex.ext <;> simp [hreal]
    let t := Real.sqrt (lambda.re+c)
    have ht : 0 < t := Real.sqrt_pos.mpr hpos
    have hs : t^2 = lambda.re+c := Real.sq_sqrt hpos.le
    have hsq : (t:ℂ)^2 = lambda+(c:ℂ) := by
      have hh : (t:ℂ)^2 = ((lambda.re+c:ℝ):ℂ) := by exact_mod_cast hs
      simpa only [Complex.ofReal_add,hval] using hh
    have hzero : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u.val) t = 0 := by
      rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u.val (c:ℂ) t hi,
        hsq,add_sub_cancel_right,hl,mul_zero]
    obtain ⟨k,hk⟩ := (mem_range_hillMiuraDiracDirichlet_iff u.val t).mpr hzero
    have hkpos : (0:ℤ) < k := (hillMiuraDiracDirichlet_re_pos_iff u k).mp (by
      rw [hk,Complex.ofReal_re]
      exact ht)
    let n : ℕ+ := ⟨k.toNat,by omega⟩
    have hnk : ((n:ℕ):ℤ) = k := by
      dsimp [n]
      exact Int.toNat_of_nonneg hkpos.le
    refine ⟨n,?_⟩
    rw [hillMiuraDirichletEnergy,hnk,hk,hsq]
    ring
  · rintro ⟨n,rfl⟩
    have hp : 0 < (hillMiuraDiracDirichlet u.val (n:ℕ)).re :=
      (hillMiuraDiracDirichlet_re_pos_iff u _).mpr (by exact_mod_cast n.property)
    apply hillHminusDirichlet_miuraDirichletEnergy_eq_zero q u.val c hi (n:ℕ)
    intro hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

/-- Squaring the positive actual canonical frequencies is strictly
increasing, so this is the correctly ordered FULL scalar zero sequence. -/
theorem strictMono_hillMiuraDirichletEnergy_re_positive
    (u : PeriodOneRealL2) (c : ℝ) :
    StrictMono (fun n : ℕ+ => (hillMiuraDirichletEnergy u.val c (n:ℕ)).re) := by
  intro i j hij
  have horder := strictMono_hillMiuraDiracDirichlet_re u
    (show ((i:ℕ):ℤ) < ((j:ℕ):ℤ) by exact_mod_cast hij)
  have hp : 0 < (hillMiuraDiracDirichlet u.val (i:ℕ)).re :=
    (hillMiuraDiracDirichlet_re_pos_iff u _).mpr (by exact_mod_cast i.property)
  have hrI := hillMiuraDiracDirichlet_im_eq_zero u (i:ℕ)
  have hrJ := hillMiuraDiracDirichlet_im_eq_zero u (j:ℕ)
  simp only [hillMiuraDirichletEnergy,pow_two,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,hrI,hrJ,mul_zero,sub_zero]
  nlinarith

end NLS.KdV
