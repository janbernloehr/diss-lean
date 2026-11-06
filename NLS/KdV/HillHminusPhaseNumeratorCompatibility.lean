import NLS.KdV.HillHminusDirichletSourcePhase
import NLS.ZakharovShabat.SourcePsiPhaseCompatibility

noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- A SINGLE complex H-minus-one neighborhood identifies ALL physical
energy numerators with the SAME checked normalized source family at the
actual ordinary Dirichlet source. The identity includes zero energy and
zero frequency; no pointwise or index-dependent shrinking is used. -/
theorem exists_common_dirichletSource_numerator_agreement (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.source ∧
      ∀ a∈U, P.dirichletSource a∈P.family.domain ∧
        ∀ n : ℕ+, (∀ E : ℂ, P.numerator n (E,a)=
          sourcePsiEnergyNumerator P.family.roots ((n:ℕ):ℤ)
            (E+P.miura.energyShift,P.dirichletSource a)) ∧
          ∀ z : ℂ, 2*z*P.numerator n (z^2-P.miura.energyShift,a)=
            sourceSelectedPsiNumerator P.family.roots ((n:ℕ):ℤ) (z,P.dirichletSource a)-
              sourceSelectedPsiNumerator P.family.roots ((n:ℕ):ℤ) (-z,P.dirichletSource a) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,hreal⟩
  let φ : realTypeSourceSubmodule 2 := ⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩
  have hp : sourcePhase φ.val∈P.family.domain :=
    P.family.real_subset (isRealType_sourcePhase φ.val φ.property)
  obtain ⟨V,hV,hφV,hVW,hphase,hmatch⟩ :=
    P.family.verified.exists_common_sourcePhase_agreement P.family.domain_open φ hq.2 hp
  let U := P.source ∩ (fun a => hillMiuraDiagonal (P.miura.lift a)) ⁻¹' V
  have hc : ContinuousOn (fun a => hillMiuraDiagonal (P.miura.lift a)) P.source :=
    hillMiuraDiagonal.continuous.comp_continuousOn
      (P.miura.lift_analytic.continuousOn.mono inter_subset_left)
  refine ⟨U,hc.isOpen_inter_preimage P.source_open hV,⟨hq,hφV⟩,inter_subset_left,?_⟩
  intro a ha
  refine ⟨hphase _ ha.2,?_⟩
  intro n
  have he (E : ℂ) : P.numerator n (E,a)=
      sourcePsiEnergyNumerator P.family.roots ((n:ℕ):ℤ)
        (E+P.miura.energyShift,P.dirichletSource a) :=
    ((hmatch _ ha.2 ((n:ℕ):ℤ)).2.2 (E+P.miura.energyShift)).symm
  refine ⟨he,?_⟩
  intro z
  rw [he,sub_add_cancel]
  exact two_mul_frequency_oddSquareDescent
    (sourceSelectedPsiNumerator P.family.roots ((n:ℕ):ℤ)) (P.dirichletSource a) z

end NLS.KdV.HillHminusPsiChart
