import NLS.KdV.HillCartesianEndpointInvariant

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- Actual finite endpoint transports preserve the normalized ORIGINAL
Cartesian bracket while retaining every original spectral constraint. -/
theorem exists_hillFiniteEndpointTransport_preserving_normalized_bracket
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0)
    (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
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
          hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) ∧
      hillIntrinsicNormalizedCartesianBracket n m σ τ r =
        hillIntrinsicNormalizedCartesianBracket n m σ τ q := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨q,hmean,rfl,(fun _ => rfl),(fun _ _ => ⟨rfl,rfl⟩),?_,?_,rfl⟩
      · intro n _ hn
        exact (Finset.notMem_empty n hn).elim
      · intro _ _ _
        exact ⟨rfl,rfl⟩
  | @insert k s hks ih =>
      have hk := hpos k (Finset.mem_insert_self k s)
      obtain ⟨r,hrmean,hrnorm,hrΔ,hrends,hrsel,hrout,hrB⟩ :=
        ih (fun n hn => hpos n (Finset.mem_insert_of_mem hn))
      have hrn : hillRealGapHalfLength r.val r.property.1 r.property.2 n ≠ 0 := by
        unfold hillRealGapHalfLength
        rw [(hrends n n.pos).1,(hrends n n.pos).2]
        exact hgapn
      have hrm : hillRealGapHalfLength r.val r.property.1 r.property.2 m ≠ 0 := by
        unfold hillRealGapHalfLength
        rw [(hrends m m.pos).1,(hrends m m.pos).2]
        exact hgapm
      obtain ⟨p,hpmean,hpnorm,hpΔ,hpends,hpκ,hpterminal,hpout,hpB⟩ :=
        exists_hillSingleEndpointTransport_preserving_normalized_bracket r hrmean n m σ τ hrn hrm k hk
      refine ⟨p,hpmean,hpnorm.trans hrnorm,?_,?_,?_,?_,hpB.trans hrB⟩
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

end NLS.KdV
