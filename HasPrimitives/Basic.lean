import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic


-- From V. Beffara https://github.com/vbeffara/RMT4
def has_primitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U


