import NLS.KdV.HillProductEquationSequence

/-! ONE joint neighborhood and ONE full sequence norm bound are chosen
BEFORE ALL numerator indices. The local quotient factory, continuous
analytic frequency lift and genuine source spectral lp bounds supply
this upgrade from pointwise lp membership. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_equation_bound (P : HillProductEquationPatch)
    (t₀ : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht₀ : t₀ ∈ P.inputDomain) :
    ∃ J : Set (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne), IsOpen J ∧ t₀ ∈ J ∧ J ⊆ P.inputDomain ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ+, ∀ t ∈ J, ‖P.equation n t‖ ≤ L := by
  let b₀ := (P.frequencySource t₀).1
  let ψ₀ := P.sourcePsi t₀.2
  obtain ⟨O,hO,hbase,Q,hQ,hquot⟩ := P.quotients.local_allDisk_quotient_bound P.isolating P.V_open
    ψ₀ (P.image t₀.2 ht₀.2).1 (P.image t₀.2 ht₀.2).2 b₀
  obtain ⟨_,_,Vm,hVm,hψm,M,hM,hm⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) ψ₀ (by norm_num : (0:ℝ) < 1)
  obtain ⟨_,_,Vg,hVg,hψg,G,hG,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) ψ₀ (by norm_num : (0:ℝ) < 1)
  let A := O ∩ (ball b₀ 1 ×ˢ (Vm ∩ Vg))
  have hA : IsOpen A := hO.inter (isOpen_ball.prod (hVm.inter hVg))
  let J := (P.inputDomain ∩ P.frequencySource ⁻¹' A) ∩ {t | ‖t.1‖ < ‖t₀.1‖+1}
  have hJ : IsOpen J := (P.analytic_frequencySource.continuousOn.isOpen_inter_preimage P.inputDomain_open hA).inter
    (isOpen_lt continuous_fst.norm continuous_const)
  let K := 2*Real.pi*(Real.pi^2*P.separation*(P.separation*Q))
  have hK : 0 ≤ K := by have hc := P.isolating.one_le; dsimp only [K]; positivity
  let L := K*(‖b₀‖+1+M+G)+(‖t₀.1‖+1)+
    (2*Real.pi*M+M^2+G^2+‖(P.parent.parent.miuraBall.actionBall.shift:ℂ)‖)
  refine ⟨J,hJ,⟨⟨ht₀,hbase,mem_ball_self (by norm_num),hψm,hψg⟩,by change ‖t₀.1‖ < ‖t₀.1‖+1; linarith⟩,
    (fun _ ht => ht.1.1),L,by dsimp only [L]; positivity,?_⟩
  intro n t ht
  obtain ⟨⟨htD,htA⟩,htd⟩ := ht
  obtain ⟨htO,htb,htm,htg⟩ := htA
  have hb : ‖hillIndependentFrequencyDisplacement ((P.parent.parent.miuraBall.actionBall.shift:ℂ),t.1)‖ ≤ ‖b₀‖+1 := by
    have hd : ‖(P.frequencySource t).1-b₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using htb
    have he := norm_le_norm_sub_add (P.frequencySource t).1 b₀
    change ‖(P.frequencySource t).1‖ ≤ _
    linarith
  have hdt : ‖t.1‖ ≤ ‖t₀.1‖+1 := htd.le
  have hmid := (hm (P.sourcePsi t.2) htm).1
  have hgap := (hg (P.sourcePsi t.2) htg).1
  have hn := P.norm_equation_le_of_quotient_bound t htD Q hQ
    (fun k z hz => hquot (P.frequencySource t) htO k z hz) n
  apply hn.trans
  change K*(_+_+_)+‖t.1‖+(2*Real.pi*_+_^2+_^2+_) ≤ L
  dsimp only [L]
  gcongr

end NLS.KdV.HillProductEquationPatch
