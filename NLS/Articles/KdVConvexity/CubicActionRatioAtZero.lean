import NLS.Articles.KdVConvexity.GlobalCanonicalMomentFamily
import NLS.KdV.HillFreeCubicActionRatio
import NLS.KdV.HillRoughScalarGermIdentity

/-! # The actual cubic action-square coefficient at every real rough source near zero

The physical L2 calculation is continued as a complex rough analytic
identity, then recovered at all real H-minus-one sources. No finite-gap
or L2 assumption survives in the resulting local identity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def realZeroRoughSource : PeriodOneRealHminusOne := ⟨0,by intro k;simp⟩

theorem exists_intrinsic_cubic_action_ratio_at_zero (n : ℕ+) :
    ∃ K : PeriodOneHminusOne → ℂ, AnalyticAt ℂ K 0 ∧ K 0=-3/(8*(n : ℂ)*Real.pi) ∧
      ∀ᶠ q : PeriodOneRealHminusOne in 𝓝 realZeroRoughSource,
        hillHminusRealGapCubicContourMoment q.val q.property n =
          (hillHminusRealGapContourMoment q.val q.property n 0)^2*K q.val := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro k;simp
  obtain ⟨K,hK,hK0,hphysical⟩ := exists_hillFree_analytic_cubic_action_ratio h0q h0r n
  obtain ⟨Ω,_hΩ,hreal,A,P,hA,hP,hvalues,_htail⟩ := exists_global_analytic_canonical_moment_family
  have hz : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k;simp
  have h0Ω : (0 : PeriodOneHminusOne) ∈ Ω := hreal hz
  let G : PeriodOneHminusOne → ℂ := fun q => (A n 0 q)^2*K q
  have hG : AnalyticAt ℂ G 0 := (hA n 0 0 h0Ω).pow 2 |>.mul hK
  have hp : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      P n (hillOriginalHminusSource p.val)=G (hillOriginalHminusSource p.val) := by
    filter_upwards [hphysical] with p hp
    have hrp := hillOriginalHminusSource_real p.val p.property.2
    have hv := hvalues (hillOriginalHminusSource p.val) hrp n
    rw [hv.2.1]
    change _=(A n 0 (hillOriginalHminusSource p.val))^2*K (hillOriginalHminusSource p.val)
    rw [(hv.1 0),hillHminusRealGapContourMoment_original_source p n 0]
    exact hp
  have he := eventuallyEq_rough_of_physical_real_germ h0q h0r (P n) G (hP n 0 h0Ω) hG hp
  have ht : Tendsto (fun q : PeriodOneRealHminusOne => q.val) (𝓝 realZeroRoughSource) (𝓝 (0 : PeriodOneHminusOne)) :=
    continuous_subtype_val.continuousAt.tendsto
  refine ⟨K,hK,hK0,?_⟩
  filter_upwards [ht.eventually he] with q hq
  have hv := hvalues q.val q.property n
  rw [hv.2.1] at hq
  change _=(A n 0 q.val)^2*K q.val at hq
  rw [hv.1 0] at hq
  exact hq

/-- With the actual Hamiltonian summand weight 8*pi*n restored, the
analytic action-square coefficient has the exact free value -3. -/
theorem exists_intrinsic_weighted_cubic_action_ratio_at_zero (n : ℕ+) :
    ∃ L : PeriodOneHminusOne → ℂ, AnalyticAt ℂ L 0 ∧ L 0=-3 ∧
      ∀ᶠ q : PeriodOneRealHminusOne in 𝓝 realZeroRoughSource,
        ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*hillHminusRealGapCubicContourMoment q.val q.property n =
          (hillHminusRealGapContourMoment q.val q.property n 0)^2*L q.val := by
  obtain ⟨K,hK,hK0,hrec⟩ := exists_intrinsic_cubic_action_ratio_at_zero n
  let c : ℂ := ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)
  let L : PeriodOneHminusOne → ℂ := fun q => c*K q
  have hL0 : L 0=-3 := by
    change c*K 0=-3
    rw [hK0]
    dsimp only [c]
    push_cast
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
    have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hn,hp]
  refine ⟨L,analyticAt_const.mul hK,hL0,?_⟩
  filter_upwards [hrec] with q hq
  rw [hq]
  change c*(_^2*K q.val)=_^2*(c*K q.val)
  ring

end NLS.Articles.KdVConvexity
