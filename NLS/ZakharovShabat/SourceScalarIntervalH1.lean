import NLS.ZakharovShabat.AKNSIntervalOperator

/-! # The scalar interval spaces in Lemma 4.2

Elements are actual functions on the closed interval [0,1]. The parameter
`sine = false` gives all classical H1 functions; `sine = true` requires
both endpoint traces to vanish. The norm is exactly the square root of
the ordinary Lebesgue integral of |f|² + |f'|². Embedding in the established
AKNS domain supplies the normed-space structure without a periodicity
assumption or a choice of values outside the interval.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat
/-- Embed a scalar interval function in its cosine or sine AKNS coordinate. -/
def sourceScalarIntervalEmbedding (sine : Bool) :
    (Icc (0 : ℝ) 1 → ℂ) →ₗ[ℂ] (Icc (0 : ℝ) 1 → ℂ × ℂ) where
  toFun f x := if sine then (0,f x) else (f x,0)
  map_add' f g := by cases sine <;> ext x <;> simp
  map_smul' c f := by cases sine <;> ext x <;> simp

theorem sourceScalarIntervalEmbedding_injective (sine : Bool) :
    Function.Injective (sourceScalarIntervalEmbedding sine) := by
  intro f g h
  funext x
  cases sine
  · exact congrArg Prod.fst (congrFun h x)
  · exact congrArg Prod.snd (congrFun h x)

/-- Actual scalar H1 functions; the sine case additionally has zero endpoint traces. -/
def sourceScalarIntervalSubmodule (sine : Bool) : Submodule ℂ (Icc (0 : ℝ) 1 → ℂ) :=
  (aknsIntervalSubmodule .dirichlet).comap (sourceScalarIntervalEmbedding sine)

theorem mem_sourceScalarIntervalSubmodule (sine : Bool) (f : Icc (0 : ℝ) 1 → ℂ) :
    f ∈ sourceScalarIntervalSubmodule sine ↔ ∃ g : ℝ → ℂ,
      HasIntervalH1Regularity g ∧ (sine = true → g 0 = 0 ∧ g 1 = 0) ∧
        ∀ x : Icc (0 : ℝ) 1, f x = g x.val := by
  change sourceScalarIntervalEmbedding sine f ∈ aknsIntervalSubmodule .dirichlet ↔ _
  rw [mem_aknsIntervalSubmodule_iff]
  constructor
  · rintro ⟨g,hg,hfg⟩
    cases sine
    · exact ⟨fun x => (g x).1, hg.fst_regular, by simp,
        fun x => congrArg Prod.fst (hfg x)⟩
    · exact ⟨fun x => (g x).2, hg.snd_regular, fun _ => ⟨hg.left,hg.right⟩,
        fun x => congrArg Prod.snd (hfg x)⟩
  · rintro ⟨g,hg,he,hfg⟩
    have hz : HasIntervalH1Regularity (fun _ : ℝ => (0 : ℂ)) := by
      simpa using hg.linearCombination hg 0 0
    cases sine
    · refine ⟨fun x => (g x,0), ⟨hg,hz,rfl,rfl⟩, ?_⟩
      intro x
      change (f x,0) = (g x.val,0)
      rw [hfg x]
    · refine ⟨fun x => (0,g x), ⟨hz,hg,(he rfl).1,(he rfl).2⟩, ?_⟩
      intro x
      change (0,f x) = (0,g x.val)
      rw [hfg x]

/-- Physical scalar H1 on [0,1], with zero traces precisely when `sine = true`. -/
def SourceScalarIntervalH1 (sine : Bool) := ↥(sourceScalarIntervalSubmodule sine)

instance (sine : Bool) : AddCommGroup (SourceScalarIntervalH1 sine) :=
  inferInstanceAs (AddCommGroup ↥(sourceScalarIntervalSubmodule sine))
instance (sine : Bool) : Module ℂ (SourceScalarIntervalH1 sine) :=
  inferInstanceAs (Module ℂ ↥(sourceScalarIntervalSubmodule sine))

def sourceScalarDomainEmbedding (sine : Bool) :
    SourceScalarIntervalH1 sine →ₗ[ℂ] AKNSIntervalDomain .dirichlet where
  toFun f := ⟨sourceScalarIntervalEmbedding sine f.val, f.property⟩
  map_add' f g := by apply Subtype.ext; exact (sourceScalarIntervalEmbedding sine).map_add _ _
  map_smul' c f := by apply Subtype.ext; exact (sourceScalarIntervalEmbedding sine).map_smul _ _

theorem sourceScalarDomainEmbedding_injective (sine : Bool) :
    Function.Injective (sourceScalarDomainEmbedding sine) := by
  intro f g h
  apply Subtype.ext
  exact sourceScalarIntervalEmbedding_injective sine (congrArg Subtype.val h)

instance (sine : Bool) : NormedAddCommGroup (SourceScalarIntervalH1 sine) :=
  NormedAddCommGroup.induced _ _ (sourceScalarDomainEmbedding sine)
    (sourceScalarDomainEmbedding_injective sine)
instance (sine : Bool) : NormedSpace ℂ (SourceScalarIntervalH1 sine) :=
  NormedSpace.induced ℂ _ _ (sourceScalarDomainEmbedding sine)

def sourceScalarDomainIsometry (sine : Bool) :
    SourceScalarIntervalH1 sine →ₗᵢ[ℂ] AKNSIntervalDomain .dirichlet where
  toLinearMap := sourceScalarDomainEmbedding sine
  norm_map' _ := rfl

def sourceScalarH1OfFunction (sine : Bool) (f : ℝ → ℂ) (hf : HasIntervalH1Regularity f)
    (he : sine = true → f 0 = 0 ∧ f 1 = 0) : SourceScalarIntervalH1 sine :=
  ⟨fun x => f x.val, (mem_sourceScalarIntervalSubmodule sine _).mpr ⟨f,hf,he,fun _ => rfl⟩⟩

/-- The transported norm is exactly the physical scalar H1 energy norm. -/
theorem norm_sourceScalarH1OfFunction (sine : Bool) (f : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (he : sine = true → f 0 = 0 ∧ f 1 = 0) :
    ‖sourceScalarH1OfFunction sine f hf he‖ = Real.sqrt (intervalH1Energy f 0 1) := by
  have hz : HasIntervalH1Regularity (fun _ : ℝ => (0 : ℂ)) := by
    simpa using hf.linearCombination hf 0 0
  change ‖sourceScalarDomainEmbedding sine (sourceScalarH1OfFunction sine f hf he)‖ = _
  cases sine
  · change ‖aknsDomainOfFunction .dirichlet (fun x => (f x,0)) ⟨hf,hz,rfl,rfl⟩‖ = _
    rw [norm_aknsDomainOfFunction]
    simp [BoundaryCondition.classicalIntervalNorm, BoundaryCondition.classicalIntervalEnergy,
      intervalH1Energy]
  · change ‖aknsDomainOfFunction .dirichlet (fun x => (0,f x)) ⟨hz,hf,(he rfl).1,(he rfl).2⟩‖ = _
    rw [norm_aknsDomainOfFunction]
    simp [BoundaryCondition.classicalIntervalNorm, BoundaryCondition.classicalIntervalEnergy,
      intervalH1Energy]

end NLS.ZakharovShabat
