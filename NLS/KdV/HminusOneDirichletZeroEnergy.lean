import NLS.KdV.HminusOneDirichletSignedSymmetry

/-! The factor z in the exact auxiliary identity introduces precisely
one auxiliary zero at zero frequency for real scalar Miura profiles.
The actual scalar Dirichlet characteristic is nonzero at that energy. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- Zero frequency of the auxiliary characteristic is not a scalar
Dirichlet zero for ANY real L2 Miura lift. Simplicity of the actual
auxiliary zero and the exact product identity prove this without a trace
of the rough lift or a smoothness hypothesis. -/
theorem quasiHillL2Dirichlet_zero_ne_zero_of_real (u : PeriodOneRealL2) :
    quasiHillL2Dirichlet u.val 0 ≠ 0 := by
  let F := auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
    (hillMiuraDiagonal u.val)
  let D := quasiHillL2Dirichlet u.val
  have he : F = fun z : ℂ => z*D (z^2) :=
    funext fun z => auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet u.val z
  have hzero : F 0 = 0 := by rw [he]; simp
  have hF : AnalyticAt ℂ F 0 :=
    analyticOnNhd_auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u.val) 0 (mem_univ _)
  have ho : analyticOrderAt F 0 = 1 :=
    analyticOrderAt_auxiliaryPeriodOneCharacteristic_eq_one_of_realType (by simp) (by norm_num)
      .dirichlet (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) 0 hzero
  have hn : deriv F 0 ≠ 0 := by
    have hd : analyticOrderAt (deriv F) 0 = 0 :=
      analyticOrderAt_deriv_of_pos hF (n := 0) (by simpa using ho)
    intro hz
    exact (hF.deriv.analyticOrderAt_ne_zero.mpr hz) hd
  have hD : AnalyticAt ℂ D 0 :=
    (analyticOnNhd_quasiHillL2Dirichlet_joint (0,u.val) (mem_univ _)).comp
      (f := fun z : ℂ => (z,u.val)) (analyticAt_id.prod analyticAt_const)
  have hd0 : HasDerivAt D (deriv D 0) ((0:ℂ)^2) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hD.differentiableAt.hasDerivAt
  have hp := (hasDerivAt_id (0:ℂ)).mul (hd0.comp 0 ((hasDerivAt_id (0:ℂ)).pow 2))
  have hd : HasDerivAt F (D 0) 0 := by
    rw [he]
    simpa using! hp
  intro hz
  apply hn
  rw [hd.deriv]
  exact hz

/-- Every scalar Dirichlet zero lies STRICTLY above minus the real
constant in any literal real shifted Miura representation. -/
theorem hillHminusDirichlet_root_above_shift
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (lambda : ℂ) (hl : hillHminusDirichlet q lambda = 0) : 0 < lambda.re+c := by
  have hne : lambda+(c:ℂ) ≠ 0 := by
    intro hz
    have hh := hl
    rw [hillHminusDirichlet_eq_miura_of_shifted_image q u.val (c:ℂ) lambda hi,hz] at hh
    exact quasiHillL2Dirichlet_zero_ne_zero_of_real u hh
  let z := Complex.sqrt (lambda+(c:ℂ))
  have hsq : z^2 = lambda+(c:ℂ) := NLS.ComplexAnalysis.complex_sqrt_sq _
  have hz : z ≠ 0 := by
    intro he
    apply hne
    rw [← hsq,he]
    norm_num
  have hs := (hillHminusDirichlet_eq_zero_iff_auxiliarySpectrum
    q u.val (c:ℂ) lambda z hi hsq hz).mp hl
  have hr := auxiliaryPeriodOneSpectrum_im_eq_zero_of_realType (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) z hs
  have hzr : z.re ≠ 0 := by
    intro he
    exact hz (Complex.ext he hr)
  have he := congrArg Complex.re hsq
  simp only [pow_two,Complex.mul_re,hr,mul_zero,sub_zero,Complex.add_re,Complex.ofReal_re] at he
  nlinarith [sq_pos_of_ne_zero hzr]

end NLS.KdV
