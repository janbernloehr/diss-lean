import NLS.Articles.KdVKdV2Frequencies.PhysicalLpFrequencyPairCharts
import NLS.SequenceSpaces.RealSequenceActionDescent
import NLS.SequenceSpaces.ScalarActionFamilyGluing

/-! Actual finite-exponent frequency packets descend through common
complex action charts and glue near the ENTIRE nonnegative weak cone.
Full sequence norm bounds are transferred before scalar gluing and retained
through actual Banach sequence realization on each original complex ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure LpFrequencyRealPair (D : GlobalRoughAbelianForwardData) (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  chart : PhysicalLpFrequencyPairChart D r
  point : Coeff 2 × Coeff 2
  mem_domain : point∈chart.physical.domain
  real_point : point∈Coeff.realPairLocus 2

namespace LpFrequencyRealPair
variable {D : GlobalRoughAbelianForwardData} {r : ℝ≥0∞} [Fact (1 ≤ r)]

def actions (a : LpFrequencyRealPair D r) : Coeff 1 := quadraticActionsExponent a.point

theorem exists_action_ball (a : LpFrequencyRealPair D r) :
    ∃ ε : ℝ, ∃ g : Coeff 1 → Coeff r, 0<ε ∧
      AnalyticOnNhd ℂ g (ball a.actions ε) ∧
      (∀ b∈ball a.actions ε, ‖g b‖≤a.chart.bound) ∧
      (∀ b∈ball a.actions ε, ∀ j : ℤ, j≤0 → g b j=0) ∧
      g a.actions=a.chart.packet a.point ∧
      ∀ b∈ball a.actions ε, b∈Coeff.nonnegativeLocus 1 →
        ∃ z : Coeff 2 × Coeff 2, z∈a.chart.physical.domain ∧ z∈Coeff.realPairLocus 2 ∧
          quadraticActionsExponent (q := 1) z=b ∧ g b=a.chart.packet z := by
  obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hbound,hrec⟩ :=
    Coeff.exists_real_sequence_action_chart (p := 2) (q := 1) (r := r) (by norm_num)
      a.chart.packet a.chart.physical.domain a.chart.physical.domain_open a.chart.analytic_packet
      (fun z hz w hw hzr hwr ha => (a.chart.packet_eq_of_real_actions a.chart z hz w hw hzr hwr ha).symm)
      a.point a.mem_domain a.real_point a.chart.bound a.chart.norm_packet
  have haT : a.actions∈T := by rw [←himage];exact mem_image_of_mem _ hzZ
  obtain ⟨ε₀,hε₀,hballT⟩ := Metric.isOpen_iff.mp hT a.actions haT
  obtain ⟨ε₁,hε₁,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (p := 2) (q := 1)
    (by norm_num) a.point a.real_point Z hZ hzZ
  let ε := min ε₀ ε₁
  have hε : 0<ε := lt_min hε₀ hε₁
  have hsub : ball a.actions ε⊆T := (ball_subset_ball (min_le_left _ _)).trans hballT
  refine ⟨ε,g,hε,hg.mono hsub,(fun b hb => hbound b (hsub hb)),?_,hrec a.point hzZ,?_⟩
  · intro b hb j hj
    have hi : b∈quadraticActionsExponent (q := 1) '' Z := by rw [himage];exact hsub hb
    obtain ⟨z,hz,rfl⟩ := hi
    rw [hrec z hz]
    exact a.chart.nonpositive z (hZU hz) j hj
  · intro b hb hbr
    obtain ⟨z,hz,hzb⟩ := hlift ⟨ball_subset_ball (min_le_right _ _) hb,hbr⟩
    exact ⟨z,hZU hz.1,hz.2,hzb,by rw [←hzb,hrec z hz.1]⟩

end LpFrequencyRealPair

theorem exists_global_physical_lp_action_packet (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) :
    ∃ U : Set (Coeff 1), ∃ G : Coeff 1 → Coeff r,
      IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ G U ∧
      (∀ b∈U, ∀ j : ℤ, j≤0 → G b j=0) ∧
      ∀ (P : PhysicalLpFrequencyPairChart D r) (z : Coeff 2 × Coeff 2),
        z∈P.physical.domain → z∈Coeff.realPairLocus 2 →
          G (quadraticActionsExponent (q := 1) z)=P.packet z := by
  classical
  let A := LpFrequencyRealPair D r
  choose ε g hε hg hbound hzero hcenter hlift using (LpFrequencyRealPair.exists_action_ball (D := D) (r := r))
  let U := ⋃ a : A, ball a.actions (ε a)
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hpos (a : A) : a.actions∈Coeff.nonnegativeLocus 1 :=
    Coeff.quadraticActions_mem_nonnegativeLocus a.point a.real_point
  let f := fun (a : A) (j : ℤ) b => g a b j
  have hf (a : A) (j : ℤ) : AnalyticOnNhd ℂ (f a j) (ball a.actions (ε a)) := by
    intro b hb
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) r j).analyticAt _).comp (hg a b hb)
  have he (a b : A) (j : ℤ) (c : Coeff 1)
      (hc : c∈ball a.actions (ε a)∩ball b.actions (ε b)) (hcr : c∈Coeff.nonnegativeLocus 1) :
      f a j c=f b j c := by
    obtain ⟨z,hz,hzr,hzc,hzg⟩ := hlift a c hc.1 hcr
    obtain ⟨w,hw,hwr,hwc,hwg⟩ := hlift b c hc.2 hcr
    change g a c j=g b c j
    rw [hzg,hwg]
    exact congrArg (fun v : Coeff r => v j)
      (a.chart.packet_eq_of_real_actions b.chart z hz w hw hzr hwr (hwc.trans hzc.symm))
  obtain ⟨F,hF,hlocal,_huniq⟩ := Coeff.exists_analytic_scalar_family_gluing (p := 2) (q := 1)
    (by norm_num) (fun a : A => a.actions) ε f hpos hf he
  obtain ⟨hval,hG⟩ := Coeff.analytic_realization_of_local_bounds (r := r) (fun b j => F j b) hU hF (by
    intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    refine ⟨ball a.actions (ε a),isOpen_ball,ha,(fun c hc => mem_iUnion.mpr ⟨a,hc⟩),a.chart.bound,?_⟩
    intro c hc
    exact ⟨g a c,(fun j => (hlocal a j hc).symm),hbound a c hc⟩)
  let G := fun b => Coeff.ofFunctionOrZero r (fun j => F j b)
  have hlocalG (a : A) (b : Coeff 1) (hb : b∈ball a.actions (ε a)) : G b=g a b := by
    ext j
    rw [hval b (mem_iUnion.mpr ⟨a,hb⟩) j,hlocal a j hb]
  refine ⟨U,G,hU,?_,hG,?_,?_⟩
  · intro b hb
    obtain ⟨P,z,hz,hzr,hzb⟩ := exists_physicalLp_pair_of_nonnegative_actions D hr b hb
    let a : A := ⟨P,z,hz,hzr⟩
    exact mem_iUnion.mpr ⟨a,by change b∈ball (quadraticActionsExponent z) (ε a);rw [hzb];exact mem_ball_self (hε a)⟩
  · intro b hb j hj
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    rw [hlocalG a b ha]
    exact hzero a b ha j hj
  · intro P z hz hzr
    let a : A := ⟨P,z,hz,hzr⟩
    exact (hlocalG a a.actions (mem_ball_self (hε a))).trans (hcenter a)

end NLS.Articles.KdVKdV2Frequencies
