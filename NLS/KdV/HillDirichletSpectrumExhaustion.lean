import NLS.KdV.HillDirichletLowerExterior
import NLS.KdV.HillDirichletLabelContinuity

/-! # Exhausting the actual Dirichlet spectrum by positive gap labels -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual ordered periodic labels are unbounded above. -/
theorem exists_hillRealLabels_gt (E : ℝ) : ∃ j : ℕ, E<hillRealLabels q hq hr j := by
  obtain ⟨n,hn⟩ := exists_nat_gt (8*‖q‖+|E|+4*‖q‖+2)
  have hnR : (2 : ℝ)<n := by linarith [norm_nonneg q,abs_nonneg E]
  have hn2 : 2≤n := by exact_mod_cast hnR.le
  have hcut : 8*‖q‖≤(n : ℝ) := by linarith [norm_nonneg q,abs_nonneg E]
  obtain ⟨p,hl,_⟩ := hillRealLabels_high_pair q hq hr n hn2 hcut
  have hloc := (p.localization q hq n (by omega) hcut).1
  have hfree : (n : ℝ)≤freeHillValue n := by
    calc
      (n : ℝ)≤(n : ℝ)^2 := by nlinarith
      _ ≤ (n : ℝ)^2*Real.pi^2 := le_mul_of_one_le_right (sq_nonneg _) (by nlinarith [Real.pi_gt_three])
      _ = _ := by simp only [freeHillValue,Int.cast_natCast];ring
  refine ⟨2*n-1,?_⟩
  rw [hl]
  linarith [(abs_le.mp hloc).1,le_abs_self E,norm_nonneg q]

/-- Every actual real Dirichlet zero lies in one positive closed gap,
including a collapsed gap or an endpoint. -/
theorem hillDirichlet_zero_mem_some_gap (x : ℝ)
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0) :
    ∃ n : ℕ, ∃ _hn : 1≤n, x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
  have hlow : hillRealLabels q hq hr 0<x :=
    lt_of_not_ge (fun hx => hillL2DirichletCharacteristic_ne_zero_at_or_below_lowest q hq hr x hx hz)
  have hex : ∃ j : ℕ, x≤hillRealLabels q hq hr (2*(j+1)) := by
    obtain ⟨j,hj⟩ := exists_hillRealLabels_gt q hq hr x
    exact ⟨j,hj.le.trans (monotone_hillRealLabels q hq hr (by omega : j≤2*(j+1)))⟩
  let n := Nat.find hex+1
  have hn : 1≤n := by dsimp only [n];omega
  have hu : x≤hillRealLabels q hq hr (2*n) := Nat.find_spec hex
  have hl : hillRealLabels q hq hr (2*n-2)<x := by
    by_cases h0 : Nat.find hex=0
    · simpa only [n,h0] using hlow
    · have hm := Nat.find_min hex (show Nat.find hex-1<Nat.find hex by omega)
      have he : Nat.find hex-1+1=Nat.find hex := by omega
      rw [he] at hm
      have hi : 2*n-2=2*Nat.find hex := by dsimp only [n];omega
      rw [hi]
      exact lt_of_not_ge hm
  refine ⟨n,hn,?_⟩
  apply hillDirichlet_zero_mem_gap_of_between_neighbor_bands q hq hr n hn x
    ⟨hl,hu.trans_lt (hillRealLabels_band_strict q hq hr n)⟩ hz

/-- The characteristic's complete zero set is precisely the positive
Dirichlet gap labels, with no lower-exterior or endpoint exception. -/
theorem hillL2DirichletCharacteristic_zero_iff_label (E : ℂ) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 ↔
      ∃ n : ℕ, ∃ hn : 1≤n, E=(hillDirichletEnergy q hq hr n hn : ℂ) := by
  constructor
  · intro hz
    have hi := hillL2DirichletCharacteristic_zero_real (SpectralWeight.one.toCoeff q) hr E hz
    have he : (E.re : ℂ)=E := by apply Complex.ext <;> simp [hi]
    have hz' : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E.re=0 := by rw [he];exact hz
    obtain ⟨n,hn,hm⟩ := hillDirichlet_zero_mem_some_gap q hq hr E.re hz'
    refine ⟨n,hn,?_⟩
    rw [hillDirichletEnergy_eq_of_zero_in_gap q hq hr n hn E.re hm hz']
    exact he.symm
  · rintro ⟨n,hn,rfl⟩
    exact hillDirichletEnergy_zero q hq hr n hn

/-- Positive Dirichlet labels as a sequence indexed without proof arguments. -/
def hillDirichletEnergySequence (j : ℕ) : ℝ := hillDirichletEnergy q hq hr (j+1) (by omega)

theorem strictMono_hillDirichletEnergySequence : StrictMono (hillDirichletEnergySequence q hq hr) := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact hillDirichletEnergy_lt_succ q hq hr (j+1) (by omega)

theorem tendsto_hillDirichletEnergySequence_atTop : Tendsto (hillDirichletEnergySequence q hq hr) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro E
  obtain ⟨j,hj⟩ := exists_hillRealLabels_gt q hq hr E
  have hm : E≤hillDirichletEnergySequence q hq hr j := by
    exact (hj.le.trans (monotone_hillRealLabels q hq hr (by omega : j≤2*(j+1)-1))).trans
      (hillDirichletEnergy_mem_gap q hq hr (j+1) (by omega)).1
  exact Filter.eventually_atTop.mpr ⟨j,fun m h => hm.trans ((strictMono_hillDirichletEnergySequence q hq hr).monotone h)⟩

theorem hillL2DirichletCharacteristic_zero_iff_sequence (E : ℂ) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 ↔
      ∃ j : ℕ, E=(hillDirichletEnergySequence q hq hr j : ℂ) := by
  rw [hillL2DirichletCharacteristic_zero_iff_label q hq hr E]
  constructor
  · rintro ⟨n,hn,hE⟩
    refine ⟨n-1,?_⟩
    simpa only [hillDirichletEnergySequence,Nat.sub_add_cancel hn] using hE
  · rintro ⟨j,hE⟩
    exact ⟨j+1,by omega,hE⟩

end NLS.KdV
