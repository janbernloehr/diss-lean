import NLS.KdV.ClassicalRoughEmbedding
import NLS.KdV.HillHminusOnePeriodBounds
import NLS.KdV.ClassicalAllContourPeriods
import NLS.ComplexAnalysis.AnalyticImplicitUniqueness

/-! # One common continuous-source neighborhood for rough critical compatibility -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N M : ℕ} {V : Set PeriodOneHminusOne}
variable {W : Set (Curve ℂ)} {A B : ℝ}
variable (Dr : HillHminusUniformPeriodData C N V A) (Dc : ClassicalAllContourPeriodData M W B)
include Dr Dc

private theorem exists_fixed_critical_compatibility (n : ℕ+) :
    ∃ U : Set (Curve ℂ), IsOpen U ∧ 0 ∈ U ∧ ∀ q ∈ U,
      hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
        classicalHillUniformCriticalPoint M n q := by
  let a : Curve ℂ → ℂ := fun q => hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q)
  let b := classicalHillUniformCriticalPoint M n
  have ha0 : a 0 = freeHillEnergy n := by dsimp only [a];rw [map_zero,Dr.critical_free]
  have hb0 : b 0 = freeHillEnergy n := Dc.critical_free n
  have ha : AnalyticAt ℂ a 0 := by
    exact (Dr.critical_analytic n (classicalHillHminusInclusion 0)
      (by simpa only [map_zero] using Dr.zero_mem)).comp
        (f := classicalHillHminusInclusion) (classicalHillHminusInclusion.analyticAt 0)
  have hb : AnalyticAt ℂ b 0 := Dc.critical_analytic n 0 Dc.zero_mem
  have hma : ∀ᶠ q in 𝓝 (0 : Curve ℂ), classicalHillHminusInclusion q ∈ V :=
    classicalHillHminusInclusion.continuous.continuousAt.eventually
      (Dr.isOpen.mem_nhds (by simpa only [map_zero] using Dr.zero_mem))
  have hza : ∀ᶠ q in 𝓝 (0 : Curve ℂ), classicalHillDiscriminantDerivative (a q,q) = 0 := by
    filter_upwards [hma] with q hq
    rw [← hillHminusDiscriminantDerivative_eq_classical]
    exact Dr.critical_zero n _ hq
  have hzb : ∀ᶠ q in 𝓝 (0 : Curve ℂ), classicalHillDiscriminantDerivative (b q,q) = 0 := by
    filter_upwards [Dc.isOpen.mem_nhds Dc.zero_mem] with q hq
    exact Dc.critical_zero n q hq
  have hs : deriv (fun z => classicalHillDiscriminantDerivative (z,0)) (a 0) ≠ 0 := by
    rw [ha0]
    exact deriv_deriv_classicalHillDiscriminant_free_energy_ne_zero n
  have he := eventuallyEq_simple_scalar_roots classicalHillDiscriminantDerivative a b 0
    (analyticOnNhd_classicalHillDiscriminantDerivative _ (mem_univ _)) ha.continuousAt hb.continuousAt
    (hb0.trans ha0.symm) hza hzb hs
  obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp he
  exact ⟨U,hU,h0U,fun q hq => hUsub hq⟩

/-- Arbitrary constructed rough and continuous all-mode families agree on one
continuous neighborhood, including every low index and the whole high tail. -/
theorem exists_critical_compatibility :
    ∃ U : Set (Curve ℂ), U ⊆ W ∧ U ⊆ classicalHillHminusInclusion ⁻¹' V ∧
      IsOpen U ∧ 0 ∈ U ∧ ∀ n : ℕ+, ∀ q ∈ U,
        hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
          classicalHillUniformCriticalPoint M n q := by
  obtain ⟨Nh,Wh,_,hWh,h0Wh,hhigh⟩ := exists_analytic_classicalHillHighCriticalPoints 0
  let K := max M Nh
  have hfixed (n : ℕ+) := Dr.exists_fixed_critical_compatibility Dc n
  let U (n : ℕ+) := (hfixed n).choose
  have hU (n : ℕ+) := (hfixed n).choose_spec
  let F : Fin (K+1) → Set (Curve ℂ) := fun i => if hi : 0 < i.val then U ⟨i.val,hi⟩ else univ
  have hF (i : Fin (K+1)) : IsOpen (F i) ∧ (0 : Curve ℂ) ∈ F i := by
    by_cases hi : 0 < i.val
    · simpa only [F,dif_pos hi] using ⟨(hU ⟨i.val,hi⟩).1,(hU ⟨i.val,hi⟩).2.1⟩
    · simp only [F,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let Z := ((W ∩ classicalHillHminusInclusion ⁻¹' V) ∩ Wh) ∩ ⋂ i, F i
  have hZ : IsOpen Z := ((Dc.isOpen.inter (Dr.isOpen.preimage classicalHillHminusInclusion.continuous)).inter hWh).inter
    (isOpen_iInter_of_finite fun i => (hF i).1)
  have h0Z : (0 : Curve ℂ) ∈ Z :=
    ⟨⟨⟨Dc.zero_mem,by simpa only [mem_preimage,map_zero] using Dr.zero_mem⟩,h0Wh⟩,
      mem_iInter.mpr (fun i => (hF i).2)⟩
  refine ⟨Z,fun _ hq => hq.1.1.1,fun _ hq => hq.1.1.2,hZ,h0Z,?_⟩
  intro n q hq
  by_cases hn : (n : ℕ) ≤ K
  · have hi := mem_iInter.mp hq.2 (⟨(n : ℕ),Nat.lt_succ_of_le hn⟩ : Fin (K+1))
    exact (hU n).2.2 q (by simpa only [F,dif_pos n.pos] using! hi)
  · have hnK := Nat.lt_of_not_ge hn
    have hnM := (le_max_left M Nh).trans_lt hnK
    have hnH := (le_max_right M Nh).trans_lt hnK
    let mu := hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q)
    have hm : mu ∈ (fun z : ℂ => z^2) '' closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
      refine ⟨sqrt mu,mem_closedBall_iff_norm.mpr ?_,complex_sqrt_sq mu⟩
      exact (Dr.critical_close n _ hq.1.1.2).le.trans (by linarith [Real.pi_pos])
    have hz : deriv (classicalHillDiscriminant q) mu = 0 := by
      change classicalHillDiscriminantDerivative (mu,q) = 0
      rw [← hillHminusDiscriminantDerivative_eq_classical]
      exact Dr.critical_zero n _ hq.1.1.2
    have he := ((hhigh n hnH).2.2 q hq.1.2).2.2.2.1 mu hm
    change mu = classicalHillUniformCriticalPoint M n q
    rw [classicalHillUniformCriticalPoint,if_neg (not_le_of_gt hnM)]
    exact he.mp hz

end HillHminusUniformPeriodData
end NLS.KdV
