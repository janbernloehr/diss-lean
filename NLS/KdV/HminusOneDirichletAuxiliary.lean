import NLS.KdV.MiuraL2DirichletAuxiliary
import NLS.KdV.HminusOneDirichletEigenstate
import NLS.SequenceSpaces.PeriodOneMiuraRealLift
import NLS.ZakharovShabat.AuxiliaryReality

/-! Exact transport from the full complex H-minus-one Dirichlet family
to the independently defined actual auxiliary Dirac operator spectrum.
Real original potentials consequently have only real Dirichlet zeros. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
open scoped ComplexConjugate
namespace NLS.KdV

/-- Literal shifted Miura transport preserves the exact auxiliary
characteristic normalization, with the physical constant energy shift. -/
theorem auxiliaryDirichlet_eq_mul_hillHminusDirichlet
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) z = z*hillHminusDirichlet q (z^2-c) := by
  rw [hillHminusDirichlet_eq_miura_of_shifted_image q u c (z^2-c) hi,
    sub_add_cancel,auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet]

/-- At any nonzero square-root energy, the rough scalar characteristic
zero criterion is the ACTUAL original auxiliary operator spectral criterion.
The auxiliary spectrum is defined by failure of bijectivity of its pencil. -/
theorem hillHminusDirichlet_eq_zero_iff_auxiliarySpectrum
    (q : PeriodOneHminusOne) (u : Coeff 2) (c lambda z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hsq : z^2 = lambda+c) (hz : z ≠ 0) :
    hillHminusDirichlet q lambda = 0 ↔
      z ∈ BoundaryCondition.auxiliarySpectrum .dirichlet (by simp)
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property := by
  rw [← auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet]
  rw [auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet,hsq,mul_eq_zero,
    ← hillHminusDirichlet_eq_miura_of_shifted_image q u c lambda hi]
  exact (or_iff_right hz).symm

/-- A real unit-period scalar lift gives a real-type original Dirac source. -/
theorem isRealType_hillMiuraDiagonal (u : PeriodOneRealL2) :
    IsRealType (CoeffPair.toMax 2 (hillMiuraDiagonal u.val)) := by
  intro n
  change (hillMiuraDiagonal u.val).snd n = conj ((hillMiuraDiagonal u.val).fst (-n))
  rw [hillMiuraDiagonal_snd,hillMiuraDiagonal_fst]
  simpa only [neg_neg] using u.property (-n)

/-- Every zero of the full H-minus-one Dirichlet characteristic of a
real original potential is real. A real shifted Miura lift is constructed
with nonzero square-root energy before applying actual operator reality. -/
theorem hillHminusDirichlet_im_eq_zero_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (lambda : ℂ) (hl : hillHminusDirichlet q lambda = 0) : lambda.im = 0 := by
  obtain ⟨c,_,u,hi,hn⟩ := exists_real_periodOneMiura_shift_avoiding q hq lambda
  let z := Complex.sqrt (lambda+(c:ℂ)^2)
  have hsq : z^2 = lambda+(c:ℂ)^2 := NLS.ComplexAnalysis.complex_sqrt_sq _
  have hz : z ≠ 0 := by
    intro he
    apply hn
    rw [← hsq,he]
    norm_num
  have hs := (hillHminusDirichlet_eq_zero_iff_auxiliarySpectrum
    q u.val ((c:ℂ)^2) lambda z hi hsq hz).mp hl
  have hr := auxiliaryPeriodOneSpectrum_im_eq_zero_of_realType (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u) z hs
  have he : (z^2).im = 0 := by
    simp only [pow_two,Complex.mul_im,hr,mul_zero,zero_mul,add_zero]
  simpa only [hsq,Complex.add_im,pow_two,Complex.mul_im,Complex.ofReal_im,
    mul_zero,zero_mul,add_zero] using he

end NLS.KdV
