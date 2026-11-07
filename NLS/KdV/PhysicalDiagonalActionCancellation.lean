import NLS.KdV.PhysicalOffDiagonalFrequency
import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.KdV.HillHminusMiuraActionMatching
import NLS.ZakharovShabat.SourceRegularDiagonalActionCancellation

/-! The exact original +6I counterterm removes the free diagonal
second-moment term. The remaining normalized errors are analytic through
closed gaps. Sequence bounds for these errors remain a further step. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem exists_regular_diagonal_action_cancellation
    (B : PhysicalMiuraFrequencyChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈B.domain) :
    ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W,
        ∃ r : ℝ, 0<r ∧
          (∀ n k : ℤ, AnalyticOnNhd ℂ (C.normalizedSecondMoment B.psi.family.roots n k)
            (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r)) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (C.regularDiagonalSecondMomentError B.psi.family.roots n)
            (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r) ∧
            AnalyticOnNhd ℂ (C.regularFirstWeightedActionError n)
              (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r)) ∧
          ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈B.domain →
            hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))∈
              ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r →
            ∀ n : ℕ+,
            let ψ := hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))
            B.correction n (hillOriginalHminusSource p.val)+
                6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ) =
              B.offDiagonalCorrection n (hillOriginalHminusSource p.val)+
                3*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n : ℤ))^2*
                  (C.regularFirstWeightedActionError (n : ℤ) ψ-
                    (n : ℂ)*C.regularDiagonalSecondMomentError B.psi.family.roots (n : ℤ) ψ)+
                12*(n : ℂ)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-(n : ℤ)))^2*
                  C.normalizedSecondMoment B.psi.family.roots (n : ℤ) (-(n : ℤ)) ψ := by
  have hqr := hillOriginalHminusSource_real q.val q.property.2
  let u : PeriodOneRealL2 := ⟨B.psi.miura.lift (hillOriginalHminusSource q.val),
    B.real_lift _ (B.domain_subset hq).1 hqr⟩
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  have hs := H.angular_extension
  obtain ⟨D,_hD⟩ := B.atlas.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension
    B.psi.family.domain_open B.psi.family.real_subset
  obtain ⟨W,_hW,_hrealW,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ
  have hC : φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨r,hr,_hsub,hN,hE,hcancel⟩ := C.exists_ball_regular_diagonal_action_cancellation
    hs.toSourcePsiIsolatingComplexExtension B.psi.family.domain_open B.atlas D φ
    (B.psi.family.real_subset φ.property) hC
  refine ⟨W,C,r,hr,hN,hE,?_⟩
  intro p hp hpball n
  let χ := hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))
  have hc := hcancel χ hpball (n : ℤ)
  have hI := B.psi.original_action_eq_twice_weighted_Dirac p (B.domain_subset hp) B.real_lift
    (B.outside_shift _ (B.domain_subset hp).1) B.shift B.energyShift_eq n
  dsimp only
  rw [hI]
  unfold correction offDiagonalCorrection
  linear_combination hc

end NLS.KdV.PhysicalMiuraFrequencyChart

namespace NLS.KdV
open scoped ComplexConjugate

theorem exists_physicalMiuraFrequencyChart_with_original_estimates
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ B : PhysicalMiuraFrequencyChart, q∈B.domain ∧ M<B.shift ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift q hq M
  obtain ⟨W,A,U,hU,_hUc,hrealU,hsub,hsum,ha,hbound⟩ :=
    P.family.exists_weighted_secondMoment_atlas H
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (P.miura.lift a)
  have hF : AnalyticOnNhd ℂ F P.miura.domain := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha)
  have hqU : F q∈U := hrealU
    (isRealType_hillMiuraDiagonal ⟨P.miura.lift q,hreal q hqP.1 hq⟩)
  obtain ⟨S,hS,hqS,hSU,K,hK,hKb⟩ := hbound (F q) hqU
  let T := P.miura.domain∩F ⁻¹' S
  have hT : IsOpen T := hF.continuousOn.isOpen_inter_preimage P.miura.domain_open hS
  have hTU (a : PeriodOneHminusOne) (ha : a∈T) : F a∈U := hSU ha.2
  let B : PhysicalMiuraFrequencyChart := {
    psi := P
    shift := c
    shift_pos := hc
    energyShift_eq := hshift
    rootNeighborhood := W
    atlas := A
    domain := T
    domain_open := hT
    domain_subset := fun a ha => ⟨ha.1,(hsub (hTU a ha)).2⟩
    real_lift := hreal
    outside_shift := houtside
    analytic_moments := fun n a haT => (ha n (F a) (hTU a haT)).comp (hF a haT.1)
    absolute_moments := fun a haT n => hsum (F a) (hTU a haT) n
    bound := K
    bound_nonneg := hK
    moment_bound := fun a haT n => hKb (F a) haT.2 n
  }
  exact ⟨B,⟨hqP.1,hqS⟩,hMc,H⟩

end NLS.KdV
