import NLS.ZakharovShabat.SourceNormalizedActionOnePlusTopology
import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceDerivative
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace

/-!
# The `ℓ^(p/2) + ℓ^(1+)` action asymptotic

For `1 < p ≤ 2`, both normalized-action deviations lie in the
projective `ℓ^(1+)` space. For `p > 2`, they lie in the Banach space
`ℓ^(p/2)`. These two cases give exact decompositions on one complex
source neighborhood for every finite `p > 1`.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both normalized-action and principal-root deviations are exactly
`ℓ^(p/2) + ℓ^(1+)` on one complex source neighborhood. The
`ℓ^(p/2)` components have locally uniform quasi-norm bounds; each
finite-exponent projection of the `ℓ^(1+)` components has a locally
uniform norm bound. -/
theorem exists_local_sourceNormalizedAction_onePlus_decomposition
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ GA GR : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)),
      ∃ BA BR : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ V, ∀ n : ℤ,
          GA ψ n + (BA ψ).1 n = sourceNormalizedActionDeviation hp hp1 ψ n ∧
          GR ψ n + (BR ψ).1 n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        ContinuousOn BA V ∧ ContinuousOn BR V ∧
        (∃ Ma Mr : ℝ, ∀ ψ ∈ V, ‖GA ψ‖ ≤ Ma ∧ ‖GR ψ‖ ≤ Mr) ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ La Lr : ℝ, ∀ ψ ∈ V,
            ‖CoeffOnePlus.toCoeff q hq1 hq (BA ψ)‖ ≤ La ∧
            ‖CoeffOnePlus.toCoeff q hq1 hq (BR ψ)‖ ≤ Lr := by
  let r := ENNReal.ofReal (p.toReal/2)
  by_cases hp2 : p ≤ 2
  · obtain ⟨V,hVopen,hφV,A,R,hcoords,hAcont,hRcont,hbounds⟩ :=
      exists_local_sourceNormalizedAction_onePlus_continuous
        hp hp1 hp2 φ hφ
    let GA : CoeffPair p → Coeff r := fun _ => 0
    let GR : CoeffPair p → Coeff r := fun _ => 0
    refine ⟨V,hVopen,hφV,GA,GR,A,R,?_,hAcont,hRcont,?_,hbounds⟩
    · intro ψ hψ n
      obtain ⟨ha,hr⟩ := hcoords ψ hψ n
      simpa only [GA,GR,Pi.zero_apply,lp.coeFn_zero,zero_add] using
        And.intro ha hr
    · exact ⟨0,0,fun ψ hψ => by simp [GA,GR]⟩
  · have hp2' : 2 < p := lt_of_not_ge hp2
    have hpr2 : 2 < p.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp).mpr hp2'
    have hrtop : r ≠ ⊤ := by simp [r]
    have hrreal : 1 < r.toReal := by
      simp only [r, ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
      linarith
    have hr1 : 1 < r :=
      (ENNReal.toReal_lt_toReal (by norm_num) hrtop).mp hrreal
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨Va,hVaopen,hφVa,FA,hFA,hFAdiff,Ma,hFAbound,_⟩ :=
      exists_local_sourceNormalizedActionDeviation_coordinateDerivative
        (q := r) hp hp1 hr1 hrtop le_rfl φ hφ
    obtain ⟨Vr,hVropen,hφVr,Mr,FR,hFR,hFRbound,_,hFRdiff⟩ :=
      exists_local_sourceNormalizedActionRootDeviation_continuousMap
        (q := r) hp hp1 hr1 hrtop le_rfl φ hφ
    let V := Va ∩ Vr
    let BA : CoeffPair p → CoeffOnePlus := fun _ => 0
    let BR : CoeffPair p → CoeffOnePlus := fun _ => 0
    refine ⟨V,hVaopen.inter hVropen,⟨hφVa,hφVr⟩,FA,FR,BA,BR,
      ?_,continuousOn_const,continuousOn_const,?_,?_⟩
    · intro ψ hψ n
      constructor
      · change FA ψ n + 0 = sourceNormalizedActionDeviation hp hp1 ψ n
        simpa using hFA ψ hψ.1 n
      · change FR ψ n + 0 = sourceNormalizedActionRootDeviation hp hp1 ψ n
        simpa using hFR ψ hψ.2 n
    · exact ⟨Ma,Mr,fun ψ hψ =>
        ⟨hFAbound ψ hψ.1,hFRbound ψ hψ.2⟩⟩
    · intro q hq1 hq
      refine ⟨0,0,?_⟩
      intro ψ hψ
      change ‖(0 : Coeff q)‖ ≤ 0 ∧ ‖(0 : Coeff q)‖ ≤ 0
      simp

end NLS.ZakharovShabat
