import NLS.KdV.HminusOneHillPsiZeroSequenceContinuity
import NLS.KdV.HillProductCoordinateVariation
import NLS.KdV.HminusOneHillProductZeroJacobian
import NLS.SequenceSpaces.PositiveDominatedCompactness

/-! ALL selections in the original real positive Hill gaps form a
compact set in the literal inverse-index l2 norm. Every actual numerator
zero sequence, including its omitted midpoint, belongs to this set. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusEnergyGapData (q : PeriodOneRealHminusOne) : Set (lp (fun _ : ℕ+ => ℂ) 2) :=
  {d | ∀ m : ℕ+, hillEnergySequenceZero m d ∈ (fun E : ℝ => (E:ℂ)) ''
    Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1)) (hillHminusLabels q.val q.property (2*(m:ℕ)))}

theorem exists_real_hill_energy_gap_selection (q : PeriodOneRealHminusOne)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData q) :
    ∃ σ : ℕ+ → ℝ, (∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ)))) ∧ ∀ m, hillEnergySequenceZero m d = (σ m:ℂ) := by
  choose σ hσ he using hd
  exact ⟨σ,hσ,fun m => (he m).symm⟩

theorem isClosed_hillHminusEnergyGapData (q : PeriodOneRealHminusOne) : IsClosed (hillHminusEnergyGapData q) := by
  simp only [hillHminusEnergyGapData,ofPred_forall]
  apply isClosed_iInter
  intro m
  apply ((isCompact_Icc.image Complex.continuous_ofReal).isClosed).preimage
  change Continuous (fun d : lp (fun _ : ℕ+ => ℂ) 2 => ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*d m)
  exact continuous_const.add (continuous_const.mul (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).continuous)

theorem norm_hillHminusEnergyGapData_le_endpoint_majorant (q : PeriodOneRealHminusOne)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData q) (m : ℕ+) :
    ‖d m‖ ≤ ‖hillHminusPositiveEndpointDisplacement false q m‖+‖hillHminusPositiveEndpointDisplacement true q m‖ := by
  obtain ⟨E,hE,he⟩ := hd m
  have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hdval : d m = ((E:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) := by
    apply (eq_div_iff hm).mpr
    change (E:ℂ) = ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*d m at he
    linear_combination -he
  let l := hillHminusLabels q.val q.property (2*(m:ℕ)-1)
  let r := hillHminusLabels q.val q.property (2*(m:ℕ))
  let y : ℝ := (Real.pi*(m:ℝ))^2
  have hbound : |E-y| ≤ |l-y|+|r-y| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (l-y),abs_nonneg (r-y),hE.1]
    · linarith [le_abs_self (r-y),abs_nonneg (l-y),hE.2]
  have hy : ((Real.pi:ℂ)*(m:ℕ))^2 = (y:ℂ) := by simp only [y,ofReal_pow,ofReal_mul,ofReal_natCast]
  rw [hdval]
  change ‖((E:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ ≤
    ‖((l:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖+‖((r:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖
  simp only [hy,norm_div,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hbound (norm_nonneg _)

theorem isCompact_hillHminusEnergyGapData (q : PeriodOneRealHminusOne) : IsCompact (hillHminusEnergyGapData q) := by
  let b := LpSequence.magnitude (hillHminusPositiveEndpointDisplacement false q)+
    LpSequence.magnitude (hillHminusPositiveEndpointDisplacement true q)
  apply LpSequence.isCompact_positive_of_isClosed_of_majorant b _ (isClosed_hillHminusEnergyGapData q)
  intro d hd m
  have hb : ‖b m‖ = ‖hillHminusPositiveEndpointDisplacement false q m‖+‖hillHminusPositiveEndpointDisplacement true q m‖ := by
    change ‖(‖hillHminusPositiveEndpointDisplacement false q m‖:ℂ)+(‖hillHminusPositiveEndpointDisplacement true q m‖:ℂ)‖ = _
    rw [← ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  rw [hb]
  exact norm_hillHminusEnergyGapData_le_endpoint_majorant q d hd m

theorem actual_hill_zero_sequence_mem_energyGapData (q : PeriodOneRealHminusOne) (n : ℕ+) :
    hillHminusPsiZeroDisplacement n q ∈ hillHminusEnergyGapData q := by
  intro m
  exact ⟨hillHminusCanonicalPsiRealZero n m q.val q.property,
    hillHminusCanonicalPsiRealZero_mem_gap n m q.val q.property,(hillEnergySequenceZero_real n m q).symm⟩

theorem exists_actual_hill_zero_sequence_convergent_subseq (q : PeriodOneRealHminusOne) (f : ℕ → ℕ+) :
    ∃ d ∈ hillHminusEnergyGapData q, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun j => hillHminusPsiZeroDisplacement (f (σ j)) q) atTop (𝓝 d) :=
  (isCompact_hillHminusEnergyGapData q).isSeqCompact (fun j => actual_hill_zero_sequence_mem_energyGapData q (f j))

end NLS.KdV
