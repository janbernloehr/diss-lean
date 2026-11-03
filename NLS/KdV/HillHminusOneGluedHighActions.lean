import NLS.KdV.HillHminusOneActionNeighborhood

/-! # Analytically glued native high Hill actions

The open domain is the union of all proved actual analytic action
neighborhoods. Cross-chart uniqueness makes the selected ratio and gap
square agree with every valid neighborhood. The resulting action is
analytic and equals every actual winding-one contour action there.
No assertion about the remaining low indices or the original global
Birkhoff map is made.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

def hillHminusHighActionDomain (n : ℕ+) : Set PeriodOneHminusOne :=
  {q | ∃ r : ℝ, ∃ K : ℂ × PeriodOneHminusOne → ℂ, ∃ V : Set PeriodOneHminusOne,
    HillHminusActionNeighborhood n r K V ∧ q ∈ V}

def hillHminusHighActionWitness (n : ℕ+) (q : PeriodOneHminusOne)
    (h : q ∈ hillHminusHighActionDomain n) :
    ℝ × (ℂ × PeriodOneHminusOne → ℂ) × Set PeriodOneHminusOne :=
  (h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.choose)

theorem hillHminusHighActionWitness_spec (n : ℕ+) (q : PeriodOneHminusOne)
    (h : q ∈ hillHminusHighActionDomain n) :
    HillHminusActionNeighborhood n (hillHminusHighActionWitness n q h).1
      (hillHminusHighActionWitness n q h).2.1 (hillHminusHighActionWitness n q h).2.2 ∧
      q ∈ (hillHminusHighActionWitness n q h).2.2 :=
  h.choose_spec.choose_spec.choose_spec

theorem HillHminusActionNeighborhood.mem_highActionDomain
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V) :
    q ∈ hillHminusHighActionDomain n := ⟨r,K,V,h,hq⟩

theorem isOpen_hillHminusHighActionDomain (n : ℕ+) : IsOpen (hillHminusHighActionDomain n) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨r,K,V,h,hq⟩
  exact Filter.mem_of_superset (h.2.1.mem_nhds hq) (fun a ha => h.mem_highActionDomain ha)

def hillHminusGluedHighActionRatio (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if h : q ∈ hillHminusHighActionDomain n then
    hillHminusNormalizedActionRatio n (hillHminusHighActionWitness n q h).1
      (hillHminusHighActionWitness n q h).2.1 q
  else 0

def hillHminusGluedHighGapSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if h : q ∈ hillHminusHighActionDomain n then
    4*hillHminusSquaredHalfGap n (hillHminusHighActionWitness n q h).1 q
  else 0

def hillHminusGluedHighAction (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusGluedHighGapSquare n q/(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighActionRatio n q

theorem HillHminusActionNeighborhood.glued_ratio_eq
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V) :
    hillHminusGluedHighActionRatio n q = hillHminusNormalizedActionRatio n r K q := by
  have hqD := h.mem_highActionDomain hq
  have hw := hillHminusHighActionWitness_spec n q hqD
  rw [hillHminusGluedHighActionRatio,dif_pos hqD]
  exact (hw.1.valid hw.2).ratio_eq (h.valid hq)

theorem HillHminusActionNeighborhood.glued_gap_square_eq
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V) :
    hillHminusGluedHighGapSquare n q = 4*hillHminusSquaredHalfGap n r q := by
  have hqD := h.mem_highActionDomain hq
  have hw := hillHminusHighActionWitness_spec n q hqD
  rw [hillHminusGluedHighGapSquare,dif_pos hqD,
    ((hw.1.valid hw.2).symmetric_data_eq (h.valid hq)).2]

theorem HillHminusActionNeighborhood.glued_gap_square_eq_pair
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V)
    (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u) :
    hillHminusGluedHighGapSquare n q = (u-l)^2 := by
  rw [h.glued_gap_square_eq hq,(hpair.symmetric_gap_data h.1).2]
  ring

theorem HillHminusActionNeighborhood.glued_action_eq_contour
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V)
    (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1) :
    hillHminusGluedHighAction n q = hillHminusHighContourAction n r K q l u Γ := by
  rw [hillHminusGluedHighAction,h.glued_gap_square_eq_pair hq l u hpair,h.glued_ratio_eq hq]
  exact ((h.valid hq).action_eq_ratio l u hpair Γ hΓ hw).symm

theorem analyticOnNhd_hillHminusGluedHighActionRatio (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusGluedHighActionRatio n) (hillHminusHighActionDomain n) := by
  rintro q ⟨r,K,V,h,hq⟩
  apply (h.analytic_ratio q hq).congr
  filter_upwards [h.2.1.mem_nhds hq] with a ha
  exact (h.glued_ratio_eq ha).symm

theorem analyticOnNhd_hillHminusGluedHighGapSquare (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusGluedHighGapSquare n) (hillHminusHighActionDomain n) := by
  rintro q ⟨r,K,V,h,hq⟩
  have hh : AnalyticAt ℂ (fun a => 4*hillHminusSquaredHalfGap n r a) q :=
    analyticAt_const.mul (h.analytic_squared_half_gap q hq)
  apply hh.congr
  filter_upwards [h.2.1.mem_nhds hq] with a ha
  exact (h.glued_gap_square_eq ha).symm

theorem analyticOnNhd_hillHminusGluedHighAction (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusGluedHighAction n) (hillHminusHighActionDomain n) :=
  ((analyticOnNhd_hillHminusGluedHighGapSquare n).div_const).mul
    (analyticOnNhd_hillHminusGluedHighActionRatio n)

theorem exists_hillHminusGluedHighAction_contour (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusHighActionDomain n) :
    ∃ r : ℝ, ∃ K : ℂ × PeriodOneHminusOne → ℂ, ∃ l u : ℂ, ∃ Γ : PiecewiseC1Loop,
      HillHminusActionChartValid n r K q ∧ HillHminusHighGapPair q n r l u ∧
      Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
      Γ.windingIntegral ((l+u)/2) = 1 ∧
      hillHminusGluedHighAction n q = hillHminusHighContourAction n r K q l u Γ := by
  obtain ⟨r,K,V,h,hqV⟩ := hq
  obtain ⟨l,u,hpair⟩ := (h.valid hqV).2.2.2.2.2.2
  obtain ⟨Γ,hΓ,hw⟩ := hpair.exists_winding_one_contour
  exact ⟨r,K,l,u,Γ,h.valid hqV,hpair,hΓ,hw,h.glued_action_eq_contour hqV l u hpair Γ hΓ hw⟩

end NLS.KdV
