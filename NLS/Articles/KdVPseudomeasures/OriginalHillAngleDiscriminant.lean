import NLS.Articles.KdVPseudomeasures.OriginalHillAngleActionKronecker
import NLS.KdV.HillAnglePairDiscriminantPeriods

/-! The actual original local Abelian angles have their exact
fixed-energy Gardner variation on one complex neighborhood before
all energies. Their pair bracket is action stationary and has an
entire spectral variation with zero prescribed action periods. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_local_Abelian_angle_discriminant_bracket
    (q : OriginalHminusOnePotential) (n : ℕ+)
    (hgap : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      C.center = originalPeriodOneCoefficients q ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain ∧ AnalyticOnNhd ℂ C.completePhase U ∧
        ∀ E : ℂ, ∀ p ∈ U,
          NLS.Poisson.hminusGardnerBracket C.completePhase (fun b => hillHminusDiscriminant b E) p =
            (1/2:ℂ)*hillHminusCanonicalPsi n (E,p) := by
  let q₀ := originalPeriodOneCoefficients q
  have hr : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q₀ hr
  obtain ⟨C,hcenter,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hgap
  obtain ⟨r,hrpos,hsub,hphase,hbr⟩ := C.exists_local_completePhase_discriminant_Gardner q₀ hCq hr
  exact ⟨P,C,hcenter,ball q₀ r,isOpen_ball,mem_ball_self hrpos,hsub,hphase,hbr⟩

theorem original_Hill_local_angle_pair_spectral_constraints
    (q : OriginalHminusOnePotential) (n m : ℕ+)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      ∃ D : HillPhysicalOnIndexPhaseChart P m,
      C.center = originalPeriodOneCoefficients q ∧ D.center = originalPeriodOneCoefficients q ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain ∧
        AnalyticOnNhd ℂ (C.completePhasePairBracket D) U ∧
        (∀ k : ℕ+, ∀ p ∈ U,
          NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D) (hillHminusCanonicalAction k) p = 0) ∧
        (∀ E : ℂ, ∀ p ∈ U,
          2*C.completePhasePairDiscriminantBracket D p E =
            NLS.Poisson.hminusGardnerBracket C.completePhase (fun b => hillHminusCanonicalPsi m (E,b)) p-
            NLS.Poisson.hminusGardnerBracket D.completePhase (fun b => hillHminusCanonicalPsi n (E,b)) p) ∧
        ∀ k : ℕ+,
          (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
            (z/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi (originalPeriodOneCoefficients q)) z)*
              C.completePhasePairDiscriminantBracket D (originalPeriodOneCoefficients q)
                (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) = 0 := by
  let q₀ := originalPeriodOneCoefficients q
  have hr : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q₀ hr
  obtain ⟨C,hcenterC,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hn
  obtain ⟨D,hcenterD,hDq⟩ := exists_hillPhysicalOnIndexPhaseChart P m q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hm
  obtain ⟨rA,hrA,hsubA,hpairA,hbrA⟩ := C.exists_local_completePhasePair_action_stationary D q₀ hCq hDq hr
  obtain ⟨rE,hrE,_,_,hbrE⟩ := C.exists_local_completePhasePair_discriminant_variation D q₀ hCq hDq hr
  let r := min rA rE
  have hrpos : 0 < r := lt_min hrA hrE
  have hsmallA : ball q₀ r ⊆ ball q₀ rA := ball_subset_ball (min_le_left _ _)
  have hsmallE : ball q₀ r ⊆ ball q₀ rE := ball_subset_ball (min_le_right _ _)
  refine ⟨P,C,D,hcenterC,hcenterD,ball q₀ r,isOpen_ball,mem_ball_self hrpos,
    (fun p hp => hsubA (hsmallA hp)),hpairA.mono hsmallA,
    (fun k p hp => (hbrA k p (hsmallA hp)).1),(fun E p hp => hbrE E p (hsmallE hp)),?_⟩
  intro k
  exact C.completePhasePairDiscriminant_prescribed_period_eq_zero D k q₀ hCq hDq hr

end NLS.Articles.KdVPseudomeasures
