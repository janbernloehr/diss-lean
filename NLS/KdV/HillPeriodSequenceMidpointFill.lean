import NLS.KdV.HillRetainedPeriodSequences
import NLS.KdV.HminusOneHillProductEquationRows

/-! Fill the omitted coordinate with the EXACT original midpoint
equation. The FULL weighted period outputs belong to lp2, with a
single finite norm bound BEFORE ALL numerator indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyMidpointDisplacement (c : ℂ) (ψ : CoeffPair 2) (n : ℕ+) : ℂ :=
  ((sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ (n:ℕ))^2+
    (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) (n:ℕ))^2/4-
      c-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)

theorem norm_hillEnergyMidpointDisplacement_le (c : ℂ) (ψ : CoeffPair 2) (n : ℕ+) :
    ‖hillEnergyMidpointDisplacement c ψ n‖ ≤
      (2*Real.pi)*‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖+
      ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖^2+
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ‖^2+‖c‖ := by
  let u := sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ ((n:ℕ):ℤ)
  let g := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ ((n:ℕ):ℤ)
  have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hn1 : (1:ℝ) ≤ ‖((n:ℕ):ℂ)‖ := by rw [Complex.norm_natCast]; exact_mod_cast n.property
  have h4n : (1:ℝ) ≤ ‖(4:ℂ)*((n:ℕ):ℂ)‖ := by rw [norm_mul,Complex.norm_ofNat]; linarith
  have he : hillEnergyMidpointDisplacement c ψ n = (2*Real.pi:ℂ)*u+u^2/(n:ℕ)+g^2/(4*(n:ℕ))-c/(n:ℕ) := by
    dsimp only [hillEnergyMidpointDisplacement,u,g]
    rw [sourcePeriodicMidpointDisplacement_apply,sourcePeriodicGapDisplacement_apply]
    change _ = (2*Real.pi:ℂ)*(sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ (n:ℕ)-(Real.pi:ℂ)*(n:ℕ))+
      (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ (n:ℕ)-(Real.pi:ℂ)*(n:ℕ))^2/(n:ℕ)+
      (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) (n:ℕ))^2/(4*(n:ℕ))-c/(n:ℕ)
    field_simp [hn]
    ring
  have hu2 : ‖u^2/((n:ℕ):ℂ)‖ ≤ ‖u‖^2 := by
    rw [norm_div,norm_pow]
    exact div_le_self (sq_nonneg _) hn1
  have hg2 : ‖g^2/((4:ℂ)*(n:ℕ))‖ ≤ ‖g‖^2 := by
    rw [norm_div,norm_pow]
    exact div_le_self (sq_nonneg _) h4n
  have hc : ‖c/((n:ℕ):ℂ)‖ ≤ ‖c‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) hn1
  have hu := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ) ((n:ℕ):ℤ)
  have hg := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ) ((n:ℕ):ℤ)
  rw [he]
  calc
    _ ≤ ‖(2*Real.pi:ℂ)*u+u^2/(n:ℕ)+g^2/(4*(n:ℕ))‖+‖c/(n:ℕ)‖ := norm_sub_le _ _
    _ ≤ ‖(2*Real.pi:ℂ)*u‖+‖u^2/(n:ℕ)‖+‖g^2/(4*(n:ℕ))‖+‖c/(n:ℕ)‖ :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ ≤ (2*Real.pi)*‖u‖+‖u‖^2+‖g‖^2+‖c‖ := by
      rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
      exact add_le_add (add_le_add (add_le_add le_rfl hu2) hg2) hc
    _ ≤ _ := by
      change ‖u‖ ≤ _ at hu
      change ‖g‖ ≤ _ at hg
      gcongr

def hillProductPeriodEquationRow (n m : ℕ+) (a R : ℤ → ℝ)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) : ℂ :=
  if m = n then t.1 n-hillEnergyMidpointDisplacement t.2.1 t.2.2 n
  else hillPeriodEquationWeight n m*hillEnergyProductJointPeriod n (a ((m:ℕ):ℤ):ℂ) (R ((m:ℕ):ℤ)) t

theorem hillProductPeriodEquationRow_eq_native (B : HillHminusPsiBall) (n m : ℕ+) (a R : ℤ → ℝ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (q : PeriodOneHminusOne) :
    hillProductPeriodEquationRow n m a R (d,((B.parent.miuraBall.actionBall.shift:ℂ),
      hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q))) =
      B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ)) (d,q) := rfl

theorem exists_hillProductPeriodEquationSequence
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (hV : IsOpen V) (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (a R : ℤ → ℝ) (hR : ∀ k, 0 < R k) (he : ∀ k, D k = Metric.ball (a k:ℂ) (R k)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+, ∃ F : lp (fun _ : ℕ+ => ℂ) 2,
      (∀ m, F m = hillProductPeriodEquationRow n m a R (d,(c,ψ))) ∧ ‖F‖ ≤ M := by
  obtain ⟨K,hK,hF⟩ := exists_hillRetainedProductPeriodSequence H hD hV ψ hψW hψV c d hplace a R hR he
  let T := ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖
  let G := ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ‖
  let M := K*(‖hillIndependentFrequencyDisplacement (c,d)‖+T+G)+‖d‖+(2*Real.pi*T+T^2+G^2+‖c‖)
  refine ⟨M,by dsimp only [M,T,G]; positivity,?_⟩
  intro n
  obtain ⟨F,hFn,hFb⟩ := hF n
  let v := d n-hillEnergyMidpointDisplacement c ψ n
  refine ⟨F+lp.single 2 n v,?_,?_⟩
  · intro m
    change F m+(lp.single 2 n v : lp (fun _ : ℕ+ => ℂ) 2) m = _
    rw [hFn,lp.single_apply]
    by_cases hmn : m = n
    · subst m
      simp only [hillRetainedProductPeriodRow,hillProductPeriodEquationRow,ite_true,Pi.single_eq_same,zero_add]
      rfl
    · simp only [hillRetainedProductPeriodRow,hillProductPeriodEquationRow,Pi.single_apply,if_neg hmn,add_zero]
  · have hv : ‖v‖ ≤ ‖d‖+(2*Real.pi*T+T^2+G^2+‖c‖) :=
      (norm_sub_le _ _).trans (add_le_add (lp.norm_apply_le_norm (by norm_num) d n)
        (norm_hillEnergyMidpointDisplacement_le c ψ n))
    calc
      _ ≤ ‖F‖+‖lp.single 2 n v‖ := norm_add_le _ _
      _ = ‖F‖+‖v‖ := by rw [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]
      _ ≤ _ := by dsimp only [M]; linarith

theorem HillHminusPsiBall.exists_productEquationSequence (B : HillHminusPsiBall)
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (hV : IsOpen V) (q : PeriodOneHminusOne) (_hq : q ∈ B.source)
    (hψW : hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q) ∈ W)
    (hψV : hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q) ∈ V)
    (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency ((B.parent.miuraBall.actionBall.shift:ℂ),d) k ∈ D k)
    (a R : ℤ → ℝ) (hR : ∀ k, 0 < R k) (he : ∀ k, D k = Metric.ball (a k:ℂ) (R k)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+, ∃ F : lp (fun _ : ℕ+ => ℂ) 2,
      (∀ m, F m = B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ)) (d,q)) ∧ ‖F‖ ≤ M := by
  obtain ⟨M,hM,hF⟩ := exists_hillProductPeriodEquationSequence H hD hV
    (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) hψW hψV
    (B.parent.miuraBall.actionBall.shift:ℂ) d hplace a R hR he
  refine ⟨M,hM,?_⟩
  intro n
  obtain ⟨F,hFn,hFb⟩ := hF n
  exact ⟨F,fun m => (hFn m).trans (hillProductPeriodEquationRow_eq_native B n m a R d q),hFb⟩

end NLS.KdV
