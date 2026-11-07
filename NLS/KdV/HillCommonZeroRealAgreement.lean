import NLS.KdV.HillCommonZeroCanonicalRoots

/-! Placed canonical roots recover the ORIGINAL real gap labels. Together
with the exact omitted midpoint row, this identifies the ENTIRE analytic
sequence on the whole real slice of the common complex ball. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem placed_canonical_zero_sequence_eq_actual (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : (d,q) ∈ P.inputDomain)
    (hF : P.equation n (d,q) = 0)
    (hroot : ∀ m : ℕ+, m ≠ n → hillHminusCanonicalPsi n (hillEnergySequenceZero m d,q) = 0) :
    d = hillHminusPsiZeroDisplacement n ⟨q,hr⟩ := by
  let a := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  have ha : (a,q) ∈ P.inputDomain := P.actual_real_graph_mem q hd.2 hr n
  have hFa : P.equation n (a,q) = 0 := P.equation_actual_real_zeros n q hd.2 hr
  apply lp.ext
  funext m
  by_cases hmn : m = n
  · subst m
    have he : P.row n n (d,q) = P.row n n (a,q) := by
      rw [← P.equation_apply n n (d,q) hd,← P.equation_apply n n (a,q) ha,hF,hFa]
    simp only [row,hillProductPeriodEquationRow,ite_true] at he
    exact sub_left_inj.mp he
  · obtain ⟨j,_,hj⟩ := (hillHminusCanonicalPsi_zero_iff_realZero n q hr _).mp (hroot m hmn)
    have henergy : hillEnergySequenceZero m d = hillEnergySequenceZero j a := by
      rw [hillEnergySequenceZero_real]
      exact hj.symm
    let c : ℂ := (P.parent.parent.miuraBall.actionBall.shift:ℂ)
    have hfreq : hillIndependentFrequency (c,d) ((m:ℕ):ℤ) = hillIndependentFrequency (c,a) ((j:ℕ):ℤ) := by
      rw [hillIndependentFrequency_positive,hillIndependentFrequency_positive,henergy]
    have hmD : hillIndependentFrequency (c,d) ((m:ℕ):ℤ) ∈ P.discs ((m:ℕ):ℤ) := hd.1.2 _
    have hjD : hillIndependentFrequency (c,a) ((j:ℕ):ℤ) ∈ P.discs ((j:ℕ):ℤ) := ha.1.2 _
    have hjm : j = m := by
      by_contra hne
      have hij : ((m:ℕ):ℤ) ≠ ((j:ℕ):ℤ) := by
        intro he
        exact hne (Subtype.ext (Int.ofNat_inj.mp he).symm)
      rw [hfreq] at hmD
      exact Set.disjoint_left.mp (P.isolating.disjoint _ _ hij) hmD hjD
    subst j
    change ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*d m = ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*a m at henergy
    exact mul_left_cancel₀ (by exact_mod_cast m.ne_zero : ((m:ℕ):ℂ) ≠ 0) (add_left_cancel henergy)

theorem common_analytic_sequence_real_agreement (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ+)
    (s : PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2)
    (hs : AnalyticOnNhd ℂ s (ball q ε))
    (hgraph : ∀ y ∈ ball q ε, (s y,y) ∈ P.inputDomain)
    (hF : ∀ y ∈ ball q ε, P.equation n (s y,y) = 0)
    (hreal : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, s a.val = hillHminusPsiZeroDisplacement n a) :
    ∀ y ∈ ball q ε, ∀ hy : IsRealPeriodOneHminusOne y,
      s y = hillHminusPsiZeroDisplacement n ⟨y,hy⟩ := by
  intro y hy hyr
  exact P.placed_canonical_zero_sequence_eq_actual n y hyr (s y) (hgraph y hy) (hF y hy)
    (fun m hmn => P.common_analytic_sequence_canonical_root q hq hr ε hε n s hs hgraph hreal m hmn y hy)

end NLS.KdV.HillProductEquationPatch
