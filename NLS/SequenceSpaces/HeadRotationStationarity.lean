import NLS.SequenceSpaces.HeadActionSection
import NLS.SequenceSpaces.LocalTailSumDescent

/-! # Rotation stationarity in finite-head coordinates

Mixed squaring retains the head linearly. Consequently a head rotation
passes through mixed squaring and tail summation with its original tangent.
Exact local recovery transports the rotation identity to the analytic
function on the finite-head/tail-sum space.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The rotation tangent of one retained head pair. -/
def headRotationVector (S : Finset ℤ) (k : S) (w : TailSumSpace q S) : TailSumSpace q S :=
  (Pi.single k (-w.2 k.val),lp.single q k.val (w.1 k))

/-- Tail summation preserves every retained-head rotation tangent. -/
theorem tailSum_rotationVector (S : Finset ℤ) (k : S) (b : Coeff q × Coeff q) :
    tailSumCLM S (actionRotationVectorCLM q k.val b) = headRotationVector S k (tailSumCLM S b) := by
  classical
  apply Prod.ext
  · funext j
    change (-lp.single (E := fun _ : ℤ => ℂ) q k.val (b.2 k.val)) j.val = _
    by_cases hj : j = k
    · subst j
      simp [headRotationVector,tailSumCLM_apply,k.property,lp.single_apply]
    · have hval : j.val ≠ k.val := fun h => hj (Subtype.ext h)
      simp [headRotationVector,hj,hval,lp.single_apply]
  · ext n
    change lp.single (E := fun _ : ℤ => ℂ) q k.val (b.1 k.val) n+
      ((-lp.single (E := fun _ : ℤ => ℂ) q k.val (b.2 k.val)) n-
        truncate S (-lp.single (E := fun _ : ℤ => ℂ) q k.val (b.2 k.val)) n) = _
    by_cases hn : n = k.val
    · subst n
      simp [headRotationVector,tailSumCLM_apply,k.property,lp.single_apply]
    · simp [headRotationVector,tailSumCLM_apply,hn,lp.single_apply]

variable [p.HolderTriple p q]

/-- A rotation line in a retained head coordinate stays linear after mixed squaring. -/
theorem pairMixedSquare_head_rotationLine (S : Finset ℤ) (k : S)
    (z : Coeff p × Coeff p) (t : ℂ) :
    pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k.val z) =
      pairMixedSquare S z+t • actionRotationVectorCLM q k.val (pairMixedSquare S z) := by
  classical
  apply Prod.ext
  · ext n
    change mixedSquare S (z.1+t • (-lp.single (E := fun _ : ℤ => ℂ) p k.val (z.2 k.val))) n =
      mixedSquare S z.1 n+t*(-lp.single (E := fun _ : ℤ => ℂ) q k.val (mixedSquare S z.2 k.val)) n
    rw [mixedSquare_apply,mixedSquare_apply]
    change (if n ∈ S then z.1 n+t*(-lp.single (E := fun _ : ℤ => ℂ) p k.val (z.2 k.val)) n
      else (z.1 n+t*(-lp.single (E := fun _ : ℤ => ℂ) p k.val (z.2 k.val)) n)^2) = _
    by_cases hn : n = k.val
    · subst n
      simp [k.property,lp.single_apply]
    · simp [hn,lp.single_apply]
  · ext n
    change mixedSquare S (z.2+t • lp.single (E := fun _ : ℤ => ℂ) p k.val (z.1 k.val)) n =
      mixedSquare S z.2 n+t*(lp.single (E := fun _ : ℤ => ℂ) q k.val (mixedSquare S z.1 k.val)) n
    rw [mixedSquare_apply,mixedSquare_apply]
    change (if n ∈ S then z.2 n+t*(lp.single (E := fun _ : ℤ => ℂ) p k.val (z.1 k.val)) n
      else (z.2 n+t*(lp.single (E := fun _ : ℤ => ℂ) p k.val (z.1 k.val)) n)^2) = _
    by_cases hn : n = k.val
    · subst n
      simp [k.property,lp.single_apply]
    · simp [hn,lp.single_apply]

theorem tailSum_mixed_head_rotationLine (S : Finset ℤ) (k : S)
    (z : Coeff p × Coeff p) (t : ℂ) :
    tailSumCLM S (pairMixedSquare (q := q) S (z+t • actionRotationVectorCLM p k.val z)) =
      tailSumCLM S (pairMixedSquare S z)+t • headRotationVector S k (tailSumCLM S (pairMixedSquare S z)) := by
  rw [pairMixedSquare_head_rotationLine,map_add,map_smul,tailSum_rotationVector]

/-- The local mixed-coordinate chart covers its whole tail-sum target. -/
theorem tailSum_mixed_image_chart_source (S : Finset ℤ) (V : Set (Coeff p × Coeff p))
    (a : Coeff q × Coeff q) (C : TailSumChart S (pairMixedSquare S '' V) a) :
    (fun z => tailSumCLM S (pairMixedSquare (q := q) S z)) ''
      (V ∩ pairMixedSquare S ⁻¹' C.source) = C.target := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact C.map_mem _ hz.2
  · intro w hw
    obtain ⟨z,hz,he⟩ := C.source_subset (C.section_mem w hw)
    refine ⟨z,⟨hz,?_⟩,?_⟩
    · change pairMixedSquare S z ∈ C.source
      rw [he]
      exact C.section_mem w hw
    · change tailSumCLM S (pairMixedSquare (q := q) S z) = w
      rw [he,tailSum_section]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The original rotation identity descends through exact local recovery. -/
theorem fderiv_headRotation_eq_zero_of_recovery
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (G : TailSumSpace q S → F)
    (U : Set (Coeff p × Coeff p)) (hU : IsOpen U) (T : Set (TailSumSpace q S)) (hT : IsOpen T)
    (hf : DifferentiableOn ℂ f U) (hG : DifferentiableOn ℂ G T)
    (hm : ∀ z ∈ U, tailSumCLM S (pairMixedSquare S z) ∈ T)
    (he : ∀ z ∈ U, G (tailSumCLM S (pairMixedSquare S z)) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ U) (k : S)
    (hr : fderiv ℂ f z (actionRotationVectorCLM p k.val z) = 0) :
    fderiv ℂ G (tailSumCLM S (pairMixedSquare S z))
      (headRotationVector S k (tailSumCLM S (pairMixedSquare S z))) = 0 := by
  let γ : ℂ → Coeff p × Coeff p := fun t => z+t • actionRotationVectorCLM p k.val z
  let b := tailSumCLM S (pairMixedSquare (q := q) S z)
  let δ : ℂ → TailSumSpace q S := fun t => b+t • headRotationVector S k b
  have hγ0 : γ 0 = z := by simp [γ]
  have hδ0 : δ 0 = b := by simp [δ]
  have hγ : HasDerivAt γ (actionRotationVectorCLM p k.val z) 0 := by
    simpa [γ] using ((hasDerivAt_id (0 : ℂ)).smul_const (actionRotationVectorCLM p k.val z)).const_add z
  have hδ : HasDerivAt δ (headRotationVector S k b) 0 := by
    simpa [δ] using ((hasDerivAt_id (0 : ℂ)).smul_const (headRotationVector S k b)).const_add b
  have hdf : HasFDerivAt f (fderiv ℂ f z) (γ 0) := by
    rw [hγ0]
    exact ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hdG : HasFDerivAt G (fderiv ℂ G b) (δ 0) := by
    rw [hδ0]
    exact ((hG b (hm z hz)).differentiableAt (hT.mem_nhds (hm z hz))).hasFDerivAt
  have hfc := hdf.comp_hasDerivAt (f := γ) 0 hγ
  have hGc := hdG.comp_hasDerivAt (f := δ) 0 hδ
  rw [hr] at hfc
  have heq : (fun t => f (γ t)) =ᶠ[𝓝 (0 : ℂ)] (fun t => G (δ t)) := by
    have hstay : ∀ᶠ t in 𝓝 (0 : ℂ), γ t ∈ U :=
      hγ.continuousAt (by simpa only [hγ0] using hU.mem_nhds hz)
    filter_upwards [hstay] with t ht
    rw [← he (γ t) ht]
    exact congrArg G (tailSum_mixed_head_rotationLine S k z t)
  exact (hGc.congr_of_eventuallyEq heq).unique hfc

end NLS.Coeff
