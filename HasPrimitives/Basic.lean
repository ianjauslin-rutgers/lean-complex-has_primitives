import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
   hasPrimitives U := by sorry

namespace Real

-- A useful function: goes from z₁ to z₂ with a speed that vanishes at the endpoints
-- Having a vanishing speed at the endpoints allows paths that are differentiable by parts to be
--  parametrized in a differentiable way
noncomputable def straightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) : ℝ → ℂ :=
  fun t => z₁ * (1 - cos (t * π / (t₂ - t₁))) + z₂ * cos (t * π / (t₂ - t₁))

#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
