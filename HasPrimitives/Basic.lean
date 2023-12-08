import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

import Mathlib.Tactic.LibrarySearch

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

-- From V. Beffara https://github.com/vbeffara/RMT4
-- integral along a curve
noncomputable def curvint (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  ∫ t in t₁..t₂, deriv γ t • f (γ t)

-- A useful function: goes from z₁ to z₂ with a speed that vanishes at the endpoints
-- Having a vanishing speed at the endpoints allows paths that are differentiable by parts to be
--  parametrized in a differentiable way
noncomputable def straightSeg (t₁ t₂ : ℝ ) (z₁ z₂ : ℂ) : ℝ → ℂ :=
  fun t => z₁ * (1 - Real.cos (t * Real.pi / (t₂ - t₁))) + z₂ * Real.cos (t * Real.pi / (t₂ - t₁))

-- straight line integral between two complex points
noncomputable def linint (z₁ z₂ : ℂ) (f : ℂ → ℂ) : ℂ :=
  curvint 0 1 f (straightSeg 0 1 z₁ z₂)

lemma diffOfIntegrals (U: Set ℂ) (hU: Convex ℝ U)
    (z₀ z₁ z₂ : ℂ) (hz₀: z₀ ∈ U) (hz₁: z₁ ∈ U) (hz₂: z₂ ∈ U)
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) :
    linint z₀ z₁ f - linint z₀ z₂ f = linint z₂ z₁ f := by
  sorry

lemma derivOfLinint (z₀ : ℂ) (f: ℂ → ℂ) (hf: Continuous f) (l: Filter ℂ):
    Asymptotics.IsLittleO l (fun h ↦ ((linint z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by
  sorry

-- trivial case: empty set
theorem hasPrimitivesOfEmpty : hasPrimitives ∅ := by
  dsimp [hasPrimitives]
  simp only [Set.eqOn_empty, and_true]
  dsimp [DifferentiableOn]
  dsimp [DifferentiableWithinAt]
  dsimp [HasFDerivWithinAt]
  dsimp [HasFDerivAtFilter]
  simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
  forall_true_left]


-- To prove the main theorem, we first prove it on a disc
-- not sure what happens if U is empty
theorem hasPrimitivesOfConvex (U: Set ℂ) (hU: Convex ℝ U) : hasPrimitives U := by
  by_cases hne : U = ∅
  · convert hasPrimitivesOfEmpty

  · intros f hf_diff
    -- get z₀
    have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
    obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
    use fun z ↦ linint z₀ z f
    constructor
    · sorry

    · intro z  hz
      have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
        intros h hinU
        refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

        exact Subtype.mem z₀
      sorry
  

-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
