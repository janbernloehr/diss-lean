import NLS.KdV.HillSingleEndpointTransport

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Any finite collection of positive physical Hill indices can be moved
simultaneously to original periodic endpoints. The resulting actual mean-zero
rough source has the same norm, discriminant at every energy and every periodic
endpoint; all unselected energies and log-norming coordinates stay fixed.
There is no open-gap or finite-gap assumption on the source. -/
theorem exists_hillFiniteEndpointTransport
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0)
    (s : Finset ℕ) (hpos : ∀ n∈s, 1≤n) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0=0 ∧ ‖r.val‖=‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ n : ℕ, 1≤n →
        hillRealLabels r.val r.property.1 r.property.2 (2*n-1)=
          hillRealLabels q.val q.property.1 q.property.2 (2*n-1) ∧
        hillRealLabels r.val r.property.1 r.property.2 (2*n)=
          hillRealLabels q.val q.property.1 q.property.2 (2*n)) ∧
      (∀ n : ℕ, ∀ hn : 1≤n, n∈s →
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=0 ∧
        (hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillRealLabels q.val q.property.1 q.property.2 (2*n-1) ∨
         hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillRealLabels q.val q.property.1 q.property.2 (2*n))) ∧
      (∀ n : ℕ, ∀ hn : 1≤n, n∉s →
        hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillDirichletEnergy q.val q.property.1 q.property.2 n hn ∧
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=
          hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨q,hmean,rfl,(fun _ => rfl),(fun _ _ => ⟨rfl,rfl⟩),?_,?_⟩
      · intro n _ hn
        exact (Finset.notMem_empty n hn).elim
      · intro _ _ _
        exact ⟨rfl,rfl⟩
  | @insert k s hks ih =>
      have hk := hpos k (Finset.mem_insert_self k s)
      obtain ⟨r,hrmean,hrnorm,hrΔ,hrends,hrsel,hrout⟩ :=
        ih (fun n hn => hpos n (Finset.mem_insert_of_mem hn))
      obtain ⟨p,hpmean,hpnorm,hpΔ,hpends,hpκ,hpterminal,hpout⟩ :=
        exists_hillSingleEndpointTransport r hrmean k hk
      refine ⟨p,hpmean,hpnorm.trans hrnorm,?_,?_,?_,?_⟩
      · intro E
        exact (hpΔ E).trans (hrΔ E)
      · intro n hn
        exact ⟨(hpends n hn).1.trans (hrends n hn).1,
          (hpends n hn).2.trans (hrends n hn).2⟩
      · intro n hn hns
        rcases Finset.mem_insert.mp hns with he | he
        · subst n
          refine ⟨hpκ,?_⟩
          rcases hpterminal with ht | ht
          · exact Or.inl (ht.trans (hrends k hk).1)
          · exact Or.inr (ht.trans (hrends k hk).2)
        · have hnk : n≠k := fun heq => hks (heq ▸ he)
          have ho := hpout n hn hnk
          have hs := hrsel n hn he
          refine ⟨ho.2.trans hs.1,?_⟩
          exact hs.2.imp (fun ht => ho.1.trans ht) (fun ht => ho.1.trans ht)
      · intro n hn hns
        have hnk : n≠k := fun he => hns (he ▸ Finset.mem_insert_self k s)
        have hnot : n∉s := fun he => hns (Finset.mem_insert_of_mem he)
        exact ⟨(hpout n hn hnk).1.trans (hrout n hn hnot).1,
          (hpout n hn hnk).2.trans (hrout n hn hnot).2⟩

/-- If only finitely many original gaps can be open, actual finite indexed
transport reaches an all-periodic source with every log-norming coordinate
zero. The source remains in the original mean-zero rough space with exactly
the original norm and discriminant. -/
theorem exists_hillFiniteGap_allPeriodicTransport
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0)
    (s : Finset ℕ) (hpos : ∀ n∈s, 1≤n)
    (hclosed : ∀ n : ℕ, 1≤n → n∉s →
      hillRealLabels q.val q.property.1 q.property.2 (2*n-1)=
        hillRealLabels q.val q.property.1 q.property.2 (2*n)) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0=0 ∧ ‖r.val‖=‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ n : ℕ, ∀ hn : 1≤n,
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=0) := by
  obtain ⟨r,hrmean,hrnorm,hrΔ,_,hrsel,hrout⟩ := exists_hillFiniteEndpointTransport q hmean s hpos
  refine ⟨r,hrmean,hrnorm,hrΔ,?_⟩
  intro n hn
  by_cases hns : n∈s
  · exact (hrsel n hn hns).1
  · exact (hrout n hn hns).2.trans
      (hillDirichletLogMultiplier_eq_zero_of_closed_gap q.val q.property.1 q.property.2 n hn
        (hclosed n hn hns))

end NLS.KdV
