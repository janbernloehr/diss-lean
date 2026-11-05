import NLS.KdV.MiuraHillPsiNumerators
import NLS.KdV.MiuraHillPsiGrowth
import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.SequenceSpaces.PeriodOneMiuraRealCharts
import NLS.KdV.HillHminusOriginalSheets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- An actual shifted Miura chart and the verified all-index numerator factory. -/
structure HillHminusPsiChart where
  miura : HillHminusMiuraChart
  family : MiuraHillPsiFamily

namespace HillHminusPsiChart

def source (P : HillHminusPsiChart) : Set PeriodOneHminusOne :=
  P.miura.domain ∩ P.miura.lift ⁻¹' P.family.source

theorem source_open (P : HillHminusPsiChart) : IsOpen P.source :=
  P.miura.lift_analytic.continuousOn.isOpen_inter_preimage P.miura.domain_open P.family.source_open

/-- The physical energy is translated by the literal chart energy shift. -/
def numerator (P : HillHminusPsiChart) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.family.numerator n (t.1+P.miura.energyShift,P.miura.lift t.2)

theorem analytic_numerator (P : HillHminusPsiChart) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.numerator n) (univ ×ˢ P.source) := by
  intro t ht
  have hl := (P.miura.lift_analytic t.2 ht.2.1).comp
    (f := fun x : ℂ × PeriodOneHminusOne => x.2) analyticAt_snd
  exact (P.family.analytic_numerator n
    (t.1+P.miura.energyShift,P.miura.lift t.2) ⟨mem_univ _,ht.2.2⟩).comp
      (f := fun x : ℂ × PeriodOneHminusOne => (x.1+P.miura.energyShift,P.miura.lift x.2))
      ((analyticAt_fst.add analyticAt_const).prod hl)

/-- Every positive period is the literal checked Dirac pullback period,
with the exact energy Jacobian 2*z and the exact 1/(2*pi) normalization. -/
theorem numerator_pullback_period (P : HillHminusPsiChart) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift q)) ((m : ℕ) : ℤ)) :
    (2*Real.pi : ℂ)⁻¹*(∮ z in C((D.center : ℂ),D.radius),
      (2*z*P.numerator n (z^2-P.miura.energyShift,q))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal (P.miura.lift q)) z)=
      if m=n then 1 else 0 := by
  have he (z : ℂ) : P.numerator n (z^2-P.miura.energyShift,q)=
      P.family.numerator n (z^2,P.miura.lift q) := by
    simp only [numerator,sub_add_cancel]
  simp_rw [he]
  exact P.family.numerator_pullback_period n m _ hq.2 D

/-- The period assertions use actual nonempty contour families at every index. -/
theorem nonempty_periodCircle (P : HillHminusPsiChart) (q : PeriodOneHminusOne)
    (hq : q∈P.source) (m : ℕ+) :
    Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift q)) ((m : ℕ) : ℤ)) :=
  P.family.nonempty_periodCircle _ hq.2 m

/-- Exact agreement with the independently constructed actual H-minus-one
Hill trace; no new spectral family is substituted. -/
theorem discriminant_eq (P : HillHminusPsiChart) (q : PeriodOneHminusOne)
    (hq : q∈P.source) (E : ℂ) :
    hillHminusDiscriminant q E=hillMiuraL2Discriminant (P.miura.lift q) (E+P.miura.energyShift) :=
  hillHminusDiscriminant_eq_chart P.miura q hq.1 E

/-- The roots used in the actual all-index numerators are analytic in the
full H-minus-one source topology. -/
theorem analytic_roots (P : HillHminusPsiChart) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q => P.family.roots n (hillMiuraDiagonal (P.miura.lift q))) P.source := by
  intro q hq
  exact (P.family.verified.analytic n _ hq.2).comp
    (f := fun q => hillMiuraDiagonal (P.miura.lift q))
      ((hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic q hq.1))

/-- ONE H-minus-one neighborhood and constant precede ALL deleted indices.
The actual root offsets have the verified quadratic-gap times l2 form. -/
theorem locally_uniform_offsets (P : HillHminusPsiChart) (q : PeriodOneHminusOne)
    (hq : q∈P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.source ∧
      ∃ B : ℝ, 0<B ∧ ∀ a∈U, ∀ n : ℤ, ∃ b : Coeff 2, b n=0 ∧
        (∀ m : ℤ, m≠n → displacedRoots (P.family.roots n (hillMiuraDiagonal (P.miura.lift a)) : Coeff 2) m=
          sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal (P.miura.lift a)) m+
            (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (hillMiuraDiagonal (P.miura.lift a)) m)^2*b m) ∧
        ‖b‖≤B := by
  obtain ⟨V,hV,hqV,hsub,B,hB,hbound⟩ := P.family.verified.locally_uniform_offsets
    (hillMiuraDiagonal (P.miura.lift q)) hq.2
  let U : Set PeriodOneHminusOne := P.miura.domain ∩
    (fun a => hillMiuraDiagonal (P.miura.lift a)) ⁻¹' V
  have hcont : ContinuousOn (fun a => hillMiuraDiagonal (P.miura.lift a)) P.miura.domain :=
    hillMiuraDiagonal.continuous.comp_continuousOn P.miura.lift_analytic.continuousOn
  exact ⟨U,hcont.isOpen_inter_preimage P.miura.domain_open hV,⟨hq.1,hqV⟩,
    (fun a ha => ⟨ha.1,hsub ha.2⟩),B,hB,fun a ha n => hbound _ ha.2 n⟩

/-- The actual numerator retains the sub-sine growth of the checked
frequency pullback, with no nonzero-energy exception in its definition. -/
theorem numerator_pullback_sub_sine_growth (P : HillHminusPsiChart) (n : ℕ+)
    (q : PeriodOneHminusOne) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ z∈sphere (0 : ℂ) (centralCircleRadius k),
      ‖(2*z*P.numerator n (z^2-P.miura.energyShift,q))/(-2*sin z)‖≤epsilon := by
  obtain ⟨K,hK⟩ := P.family.numerator_pullback_sub_sine_growth n (P.miura.lift q) epsilon hepsilon
  refine ⟨K,?_⟩
  simpa only [numerator,sub_add_cancel] using hK

/-- At the actual original physical source the full energy trace agrees
with this SAME shifted Miura trace, including its zero-energy value. -/
theorem original_discriminant_eq (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source) (E : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E=
      hillMiuraL2Discriminant (P.miura.lift (hillOriginalHminusSource q.val)) (E+P.miura.energyShift) :=
  (hillHminusDiscriminant_original_source_agreement q.val q.property.1 E).symm.trans
    (P.discriminant_eq _ hq E)

end HillHminusPsiChart

/-- Actual common all-index numerator charts exist at every real H-minus-one
source, with a proved positive energy shift as large as requested. -/
theorem exists_hillHminusPsiChart (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, 0<c ∧ M<c ∧
      P.miura.energyShift=(c : ℂ)^2 ∧ q∈P.source ∧
      ∀ j : ℤ, P.miura.lift q (-j)=conj (P.miura.lift q j) := by
  obtain ⟨c,hc,hMc,V,hV,hqV,u,hu,hreal,himage⟩ := exists_real_periodOneMiura_energyChart q hq M
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  let C : HillHminusMiuraChart := ⟨V,hV,(c : ℂ)^2,u,hu,himage⟩
  let P : HillHminusPsiChart := ⟨C,A⟩
  have hA : u q∈A.source := A.real_mem_source ⟨u q,hreal⟩
  exact ⟨P,c,hc,hMc,rfl,⟨hqV,hA⟩,hreal⟩

/-- The common chart applies in particular to every original real rough
Hill source, with the original raw-coefficient inclusion. -/
theorem exists_hillOriginal_common_hminus_psi_chart
    (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, 0<c ∧ M<c ∧
      P.miura.energyShift=(c : ℂ)^2 ∧ hillOriginalHminusSource q.val∈P.source := by
  obtain ⟨P,c,hc,hMc,he,hq,_⟩ := exists_hillHminusPsiChart
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) M
  exact ⟨P,c,hc,hMc,he,hq⟩

/-- The actual numerator chart may simultaneously retain all verified
original all-index estimates needed for the normal phase series. -/
theorem exists_hillHminusPsiChart_with_original_estimates (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, 0<c ∧ M<c ∧
      P.miura.energyShift=(c : ℂ)^2 ∧ q∈P.source ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots := by
  obtain ⟨c,hc,hMc,V,hV,hqV,u,hu,hreal,himage⟩ := exists_real_periodOneMiura_energyChart q hq M
  obtain ⟨A,hA⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let C : HillHminusMiuraChart := ⟨V,hV,(c : ℂ)^2,u,hu,himage⟩
  let P : HillHminusPsiChart := ⟨C,A⟩
  have hsource : u q∈A.source := A.real_mem_source ⟨u q,hreal⟩
  exact ⟨P,c,hc,hMc,rfl,⟨hqV,hsource⟩,hA⟩

end NLS.KdV
