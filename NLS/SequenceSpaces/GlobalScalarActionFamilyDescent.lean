import NLS.SequenceSpaces.RealScalarActionFamilyDescent
import NLS.SequenceSpaces.ScalarActionFamilyGluing
import NLS.SequenceSpaces.RealActionLifting

/-! # Common global action extension of real-invariant scalar families

Analyticity near all real coordinate pairs, invariance on real action
fibers, and local quadratic tail bounds imply analytic factors on one
complex neighborhood of the entire nonnegative action cone. No common
global action domain is assumed. The local tail estimates survive gluing.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal Classical
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Construct the common action domain from the original real-invariant
family and its local coordinate-space tail bounds. -/
theorem exists_global_scalar_action_family_with_tail_bounds {ι : Type*} (hp : p ≠ ⊤)
    (J : ι → Coeff q → ℂ) (f : ι → (Coeff p × Coeff p) → ℂ)
    (U : Set (Coeff p × Coeff p)) (_hU : IsOpen U) (hrealU : realPairLocus p ⊆ U)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hinv : ∀ i, ∀ z ∈ U, ∀ w ∈ U,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      quadraticActionsExponent (q := q) w = quadraticActionsExponent z → f i w = f i z)
    (hbound : ∀ z ∈ realPairLocus p,
      ∃ W : Set (Coeff p × Coeff p), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ W, ∀ i ∉ s,
          ‖f i w‖ ≤ C*‖J i (quadraticActionsExponent (q := q) w)‖^2) :
    ∃ V : Set (Coeff q), ∃ G : ι → Coeff q → ℂ,
      IsOpen V ∧ nonnegativeLocus q ⊆ V ∧
      (∀ i, AnalyticOnNhd ℂ (G i) V) ∧
      (∀ i, ∀ z ∈ realPairLocus p, G i (quadraticActionsExponent z) = f i z) ∧
      ∀ b ∈ V, ∃ T : Set (Coeff q), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ i ∉ s,
          ‖G i c‖ ≤ C*‖J i c‖^2 := by
  classical
  let A := nonnegativeLocus q
  have hlift (a : A) : ∃ z : Coeff p × Coeff p,
      z ∈ realPairLocus p ∧ quadraticActionsExponent (q := q) z = a.val := by
    obtain ⟨z,hz,he,_⟩ := exists_real_quadraticActions_lift hp a.val a.property
    exact ⟨z,hz,he⟩
  choose z hzreal hza using hlift
  have hlocal (a : A) : ∃ r : ℝ, ∃ g : ι → Coeff q → ℂ,
      0 < r ∧ (∀ i, AnalyticOnNhd ℂ (g i) (ball a.val r)) ∧
      (∀ i, ∀ b : A, b.val ∈ ball a.val r → g i b.val = f i (z b)) ∧
      ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ball a.val r, ∀ i ∉ s,
        ‖g i b‖ ≤ C*‖J i b‖^2 := by
    obtain ⟨W,hW,hzW,hWU,s,C,hC,hb⟩ := hbound (z a) (hzreal a)
    obtain ⟨Z,T,g,hZ,hzZ,hZW,hT,himage,hg,hrec⟩ :=
      exists_real_scalar_action_family_chart (q := q) hp f W hW
        (fun i => (hf i).mono hWU)
        (fun i u hu v hv => hinv i u (hWU hu) v (hWU hv)) (z a) hzW (hzreal a)
    have haT : a.val ∈ T := by rw [← himage]; exact ⟨z a,hzZ,hza a⟩
    obtain ⟨r₀,hr₀,hballT⟩ := Metric.isOpen_iff.mp hT a.val haT
    obtain ⟨r₁,hr₁,hrealLift⟩ := exists_ball_real_quadraticActions_lifts (q := q) hp
      (z a) (hzreal a) Z hZ hzZ
    let r := min r₀ r₁
    have hr : 0 < r := lt_min hr₀ hr₁
    have hsmallT : ball a.val r ⊆ T := (ball_subset_ball (min_le_left _ _)).trans hballT
    have hsmallReal : ball a.val r ∩ nonnegativeLocus q ⊆
        quadraticActionsExponent '' (Z ∩ realPairLocus p) := by
      intro b hb
      apply hrealLift
      refine ⟨?_,hb.2⟩
      simpa only [hza a] using ball_subset_ball (min_le_right r₀ r₁) hb.1
    refine ⟨r,g,hr,fun i => (hg i).mono hsmallT,?_,s,C,hC,?_⟩
    · intro i b hbball
      obtain ⟨w,hw,hew⟩ := hsmallReal ⟨hbball,b.property⟩
      have hgw : g i b.val = f i w := by rw [← hew]; exact hrec i w hw.1
      exact hgw.trans (hinv i (z b) (hrealU (hzreal b)) w (hWU (hZW hw.1))
        (hzreal b) hw.2 (hew.trans (hza b).symm))
    · intro b hbball i hi
      obtain ⟨w,hw,hew⟩ := himage.symm ▸ hsmallT hbball
      rw [← hew,hrec i w hw]
      exact hb w (hZW hw) i hi
  choose r g hr hg hrec s C hC htail using hlocal
  let V : Set (Coeff q) := ⋃ a : A, ball a.val (r a)
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_ball)
  have hcone : nonnegativeLocus q ⊆ V := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hr ⟨a,ha⟩)⟩
  have he (a b : A) (i : ι) (c : Coeff q)
      (hc : c ∈ ball a.val (r a) ∩ ball b.val (r b)) (hcpos : c ∈ nonnegativeLocus q) :
      g a i c = g b i c :=
    (hrec a i ⟨c,hcpos⟩ hc.1).trans (hrec b i ⟨c,hcpos⟩ hc.2).symm
  obtain ⟨G,hG,hlocalG,_⟩ := exists_analytic_scalar_family_gluing (q := q) hp
    (fun a : A => a.val) r g (fun a => a.property) hg he
  refine ⟨V,G,hV,hcone,hG,?_,?_⟩
  · intro i w hwr
    let a : A := ⟨quadraticActionsExponent w,quadraticActions_mem_nonnegativeLocus w hwr⟩
    have ha : a.val ∈ ball a.val (r a) := mem_ball_self (hr a)
    have heq : G i a.val = f i (z a) := (hlocalG a i ha).trans (hrec a i a ha)
    exact heq.trans (hinv i w (hrealU hwr) (z a) (hrealU (hzreal a))
      hwr (hzreal a) (hza a))
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    refine ⟨ball a.val (r a),isOpen_ball,ha,fun c hc => mem_iUnion.mpr ⟨a,hc⟩,
      s a,C a,hC a,?_⟩
    intro c hc i hi
    rw [hlocalG a i hc]
    exact htail a c hc i hi

end NLS.Coeff
