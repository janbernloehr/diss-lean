import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.SequenceSpaces.PhysicalRealImag
import NLS.ComplexAnalysis.RealFormBallGluing

/-! # The physical real form of unit-period H^-1 potentials

Raw Fourier reality is the fixed locus of physical conjugate reflection.
The real and imaginary parts are continuous norm contractions with an
exact complex decomposition. Analytic local families centered at real
potentials therefore glue on the entire union of their balls.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS

theorem IsRealPeriodOneHminusOne.add {a b : PeriodOneHminusOne}
    (ha : IsRealPeriodOneHminusOne a) (hb : IsRealPeriodOneHminusOne b) :
    IsRealPeriodOneHminusOne (a+b) := by
  intro k
  simp only [WeightedCoeff.add_val,ha k,hb k,map_add]

theorem isRealPeriodOneHminusOne_iff_conjugateReflection (q : PeriodOneHminusOne) :
    IsRealPeriodOneHminusOne q ↔
      WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) q = q := by
  constructor
  · intro h
    apply Subtype.ext
    funext k
    simp only [WeightedCoeff.conjugateReflection_apply,h k,Complex.conj_conj]
  · intro h k
    have he := congrArg (fun a : PeriodOneHminusOne => a.val (-k)) h
    simpa only [WeightedCoeff.conjugateReflection_apply,neg_neg] using he.symm

abbrev periodOneHminusRealPart : PeriodOneHminusOne → PeriodOneHminusOne :=
  WeightedCoeff.physicalRealPart (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))

abbrev periodOneHminusImagPart : PeriodOneHminusOne → PeriodOneHminusOne :=
  WeightedCoeff.physicalImagPart (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))

theorem isReal_periodOneHminusRealPart (q : PeriodOneHminusOne) :
    IsRealPeriodOneHminusOne (periodOneHminusRealPart q) :=
  (isRealPeriodOneHminusOne_iff_conjugateReflection _).mpr
    (WeightedCoeff.conjugateReflection_physicalRealPart _ _ q)

theorem isReal_periodOneHminusImagPart (q : PeriodOneHminusOne) :
    IsRealPeriodOneHminusOne (periodOneHminusImagPart q) :=
  (isRealPeriodOneHminusOne_iff_conjugateReflection _).mpr
    (WeightedCoeff.conjugateReflection_physicalImagPart _ _ q)

theorem convex_realPeriodOneHminusOne : Convex ℝ {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q} := by
  intro x hx y hy a b _ _ _
  change IsRealPeriodOneHminusOne ((a : ℂ) • x+(b : ℂ) • y)
  exact (hx.smul_real a).add (hy.smul_real b)

/-- Banach-valued local analytic functions glue from actual real potential
agreement on overlaps. The common domain depends only on the real balls. -/
theorem exists_analyticOnNhd_gluing_realHminus
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} (a : ι → PeriodOneRealHminusOne) (r : ι → ℝ)
    (f : ι → PeriodOneHminusOne → F)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball (a i).val (r i)))
    (he : ∀ i j c, c ∈ ball (a i).val (r i) ∩ ball (a j).val (r j) →
      IsRealPeriodOneHminusOne c → f i c = f j c) :
    ∃ G : PeriodOneHminusOne → F, AnalyticOnNhd ℂ G (⋃ i, ball (a i).val (r i)) ∧
      (∀ i, EqOn G (f i) (ball (a i).val (r i))) ∧
      (∀ H : PeriodOneHminusOne → F, (∀ i, EqOn H (f i) (ball (a i).val (r i))) →
        EqOn H G (⋃ i, ball (a i).val (r i))) := by
  exact ComplexAnalysis.exists_analyticOnNhd_gluing_continuous_real_form
    {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q} convex_realPeriodOneHminusOne
    (fun _ _ hx hy => hx.add hy) (fun t _ hx => hx.smul_real t)
    periodOneHminusRealPart periodOneHminusImagPart isReal_periodOneHminusRealPart isReal_periodOneHminusImagPart
    (fun q => (WeightedCoeff.physicalRealPart_add_I_physicalImagPart _ _ q).symm)
    (WeightedCoeff.continuous_physicalRealPart _ _).continuousAt (WeightedCoeff.physicalRealPart_zero _ _)
    (WeightedCoeff.continuous_physicalImagPart _ _).continuousAt (WeightedCoeff.physicalImagPart_zero _ _)
    (fun i => (a i).val) r f (fun i => (a i).property) hf he

end NLS
