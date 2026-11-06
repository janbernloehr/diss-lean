import NLS.SequenceSpaces.GlobalScalarActionFamilyDescent

/-! # Global scalar action descent from independent local coordinate germs -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Coeff

/-- A full family of independent local coordinate germs, one over every
nonnegative action point, glues with its quadratic tail estimates. No
single coordinate inverse near all real pairs is required. -/
theorem exists_global_scalar_action_family_of_local_real_germs
    {ι : Type*} (F : ι → nonnegativeLocus 1 → ℂ) (J : ι → Coeff 1 → ℂ)
    (hlocal : ∀ a : nonnegativeLocus 1,
      ∃ z : Coeff 2 × Coeff 2, ∃ U : Set (Coeff 2 × Coeff 2),
      ∃ f : ι → (Coeff 2 × Coeff 2) → ℂ,
        z ∈ realPairLocus 2 ∧ quadraticActionsExponent (q := 1) z = a.val ∧
        IsOpen U ∧ z ∈ U ∧ (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
        (∀ i u, u ∈ U → ∀ hr : u ∈ realPairLocus 2,
          f i u = F i ⟨quadraticActionsExponent u,quadraticActions_mem_nonnegativeLocus u hr⟩) ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ U, ∀ i ∉ s,
          ‖f i u‖ ≤ C*‖J i (quadraticActionsExponent u)‖^2) :
    ∃ V : Set (Coeff 1), ∃ G : ι → Coeff 1 → ℂ,
      IsOpen V ∧ nonnegativeLocus 1 ⊆ V ∧
      (∀ i, AnalyticOnNhd ℂ (G i) V) ∧
      (∀ i a, G i a.val = F i a) ∧
      ∀ b ∈ V, ∃ T : Set (Coeff 1), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ i ∉ s,
          ‖G i c‖ ≤ C*‖J i c‖^2 := by
  classical
  have hcharts (a : nonnegativeLocus 1) :
      ∃ r : ℝ, ∃ g : ι → Coeff 1 → ℂ,
        0 < r ∧ (∀ i, AnalyticOnNhd ℂ (g i) (ball a.val r)) ∧
        (∀ i (b : nonnegativeLocus 1), b.val ∈ ball a.val r → g i b.val = F i b) ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ball a.val r, ∀ i ∉ s,
          ‖g i b‖ ≤ C*‖J i b‖^2 := by
    obtain ⟨z,U,f,hzr,hza,hU,hzU,hf,hrec,s,C,hC,hb⟩ := hlocal a
    have hinv (i : ι) (u : Coeff 2 × Coeff 2) (hu : u ∈ U)
        (v : Coeff 2 × Coeff 2) (hv : v ∈ U)
        (hur : u ∈ realPairLocus 2) (hvr : v ∈ realPairLocus 2)
        (he : quadraticActionsExponent (q := 1) v = quadraticActionsExponent u) : f i v = f i u := by
      rw [hrec i v hv hvr,hrec i u hu hur]
      exact congrArg (F i) (Subtype.ext he)
    obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hgRec⟩ :=
      exists_real_scalar_action_family_chart (p := 2) (q := 1) (by norm_num)
        f U hU hf hinv z hzU hzr
    have haT : a.val ∈ T := by rw [←himage]; exact ⟨z,hzZ,hza⟩
    obtain ⟨r0,hr0,hballT⟩ := Metric.isOpen_iff.mp hT a.val haT
    obtain ⟨r1,hr1,hlift⟩ := exists_ball_real_quadraticActions_lifts (p := 2) (q := 1)
      (by norm_num) z hzr Z hZ hzZ
    let r := min r0 r1
    have hr : 0 < r := lt_min hr0 hr1
    have hBT : ball a.val r ⊆ T := (ball_subset_ball (min_le_left _ _)).trans hballT
    refine ⟨r,g,hr,fun i => (hg i).mono hBT,?_,s,C,hC,?_⟩
    · intro i b hbball
      have hnear : b.val ∈ ball (quadraticActionsExponent (q := 1) z) r1 := by
        rw [hza]
        exact ball_subset_ball (min_le_right r0 r1) hbball
      obtain ⟨u,hu,heu⟩ := hlift ⟨hnear,b.property⟩
      rw [←heu,hgRec i u hu.1,hrec i u (hZU hu.1) hu.2]
      exact congrArg (F i) (Subtype.ext heu)
    · intro b hbball i hi
      obtain ⟨u,hu,heu⟩ := himage.symm ▸ hBT hbball
      rw [←heu,hgRec i u hu]
      exact hb u (hZU hu) i hi
  choose r g hr hg hrec s C hC hb using hcharts
  let V : Set (Coeff 1) := ⋃ a : nonnegativeLocus 1, ball a.val (r a)
  obtain ⟨G,hG,hGrec,_⟩ := exists_analytic_scalar_family_gluing (p := 2) (q := 1)
    (by norm_num) (fun a : nonnegativeLocus 1 => a.val) r g (fun a => a.property) hg
    (by intro a b i c hc hcr; exact (hrec a i ⟨c,hcr⟩ hc.1).trans (hrec b i ⟨c,hcr⟩ hc.2).symm)
  refine ⟨V,G,isOpen_iUnion fun _ => isOpen_ball,?_,hG,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hr ⟨a,ha⟩)⟩
  · intro i a
    exact (hGrec a i (mem_ball_self (hr a))).trans (hrec a i a (mem_ball_self (hr a)))
  · intro b hbin
    obtain ⟨a,ha⟩ := mem_iUnion.mp hbin
    refine ⟨ball a.val (r a),isOpen_ball,ha,fun c hc => mem_iUnion.mpr ⟨a,hc⟩,
      s a,C a,hC a,?_⟩
    intro c hc i hi
    rw [hGrec a i hc]
    exact hb a c hc i hi

end NLS.Coeff
