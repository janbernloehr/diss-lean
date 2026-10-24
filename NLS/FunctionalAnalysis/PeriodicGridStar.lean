import NLS.FunctionalAnalysis.IntegerGridStarMultiplicity
import NLS.FunctionalAnalysis.AddCircleGridMap

/-! # Finite periodic covers from integer-grid stars

Project the grid stars to a product of unit circles, indexing vertices by
residues modulo a positive mesh denominator. Their lifts preserve the
integer-grid overlap bound.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis
universe u v
variable {ι : Type u}

/-- A grid star projected to the product of unit additive circles. -/
def periodicGridStar (M : ℕ) (v : ι → Fin M) : Set (ι → AddCircle (1 : ℝ)) :=
  addCircleGridMap M '' integerGridStar (fun i => (v i : ℤ))

theorem isOpen_periodicGridStar [Fintype ι] {M : ℕ} (hM : 0 < M) (v : ι → Fin M) :
    IsOpen (periodicGridStar M v) :=
  isOpenMap_addCircleGridMap hM _ (isOpen_integerGridStar _)

/-- Every integer vertex has a unique representative in the finite residue grid. -/
theorem integerGridVertex_residue {M : ℕ} (hM : 0 < M) (a : ι → ℤ) :
    ∃ (v : ι → Fin M) (k : ι → ℤ), ∀ i, a i = (v i : ℤ) + M * k i := by
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have h0 (i) := Int.emod_nonneg (a i) (ne_of_gt hMZ)
  have h1 (i) := Int.emod_lt_of_pos (a i) hMZ
  let v : ι → Fin M := fun i => ⟨(a i % M).toNat,by have := h0 i; have := h1 i; omega⟩
  refine ⟨v,fun i => a i / M,fun i => ?_⟩
  change a i = ((a i % M).toNat : ℤ) + M * (a i / M)
  rw [Int.toNat_of_nonneg (h0 i)]
  exact (Int.emod_add_mul_ediv (a i) M).symm

/-- The periodic stars cover every point of the circle product. -/
theorem exists_mem_periodicGridStar {M : ℕ} (hM : 0 < M) (z : ι → AddCircle (1 : ℝ)) :
    ∃ v : ι → Fin M, z ∈ periodicGridStar M v := by
  obtain ⟨x,rfl⟩ := addCircleGridMap_surjective hM z
  obtain ⟨v,k,hk⟩ := integerGridVertex_residue hM (fun i => ⌊x i⌋)
  let t : ι → ℤ := fun i => -(M : ℤ) * k i
  let y : ι → ℝ := fun i => x i + t i
  have hv : (fun i => ⌊x i⌋) + t = (fun i => (v i : ℤ)) := by
    funext i
    simp only [Pi.add_apply,t,hk i]
    ring
  refine ⟨v,y,?_,?_⟩
  · have hy := (integerGridStar_translate x (fun i => ⌊x i⌋) t).mpr (mem_integerGridStar_floor x)
    simpa only [hv] using hy
  · apply (addCircleGridMap_eq_iff hM y x).mpr
    refine ⟨fun i => -k i,fun i => ?_⟩
    simp only [y,t,Int.cast_mul,Int.cast_neg,Int.cast_natCast]
    ring

/-- A prescribed lift of a point in a periodic star lies in an integer translate of it. -/
theorem mem_periodicGridStar_lift {M : ℕ} (hM : 0 < M) (x : ι → ℝ) (v : ι → Fin M)
    (h : addCircleGridMap M x ∈ periodicGridStar M v) :
    ∃ k : ι → ℤ, x ∈ integerGridStar (fun i => (v i : ℤ) - M * k i) := by
  obtain ⟨y,hy,he⟩ := h
  obtain ⟨k,hk⟩ := (addCircleGridMap_eq_iff hM y x).mp he
  refine ⟨k,?_⟩
  let w : ι → ℤ := fun i => (v i : ℤ) - M * k i
  let t : ι → ℤ := fun i => M * k i
  have hw : w+t = (fun i => (v i : ℤ)) := by ext i; simp [w,t]
  have hx : (fun i => x i + (t i : ℝ)) = y := by
    funext i
    simpa only [t,Int.cast_mul,Int.cast_natCast] using (hk i).symm
  apply (integerGridStar_translate x w t).mp
  simpa only [hw,hx] using hy

/-- At most n+1 distinct periodic grid stars contain any point. -/
theorem card_le_of_mem_periodicGridStar [Fintype ι] {κ : Type v} [Fintype κ]
    {M : ℕ} (hM : 0 < M) (z : ι → AddCircle (1 : ℝ)) (f : κ → (ι → Fin M))
    (hf : Function.Injective f) (hmem : ∀ k, z ∈ periodicGridStar M (f k)) :
    Fintype.card κ ≤ Fintype.card ι + 1 := by
  obtain ⟨x,rfl⟩ := addCircleGridMap_surjective hM z
  choose k hk using fun j => mem_periodicGridStar_lift hM x (f j) (hmem j)
  let w : κ → (ι → ℤ) := fun j i => (f j i : ℤ) - M * k j i
  apply card_le_of_mem_integerGridStar x w ?_ hk
  intro a b he
  apply hf
  funext i
  apply Fin.ext
  have hi := congrFun he i
  change (f a i : ℤ) - M * k a i = (f b i : ℤ) - M * k b i at hi
  have hm := congrArg (fun t : ℤ => t % M) hi
  have ha0 : (0 : ℤ) ≤ f a i := by positivity
  have hb0 : (0 : ℤ) ≤ f b i := by positivity
  have ha1 : (f a i : ℤ) < M := by exact_mod_cast (f a i).isLt
  have hb1 : (f b i : ℤ) < M := by exact_mod_cast (f b i).isLt
  simpa only [Int.sub_emod,Int.mul_emod_right,sub_zero,
    Int.emod_eq_of_lt ha0 ha1,Int.emod_eq_of_lt hb0 hb1,Int.natCast_inj] using hm

end NLS.FunctionalAnalysis
