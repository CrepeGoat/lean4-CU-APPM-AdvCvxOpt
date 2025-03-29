import Init.Prelude

import CvxOpt._00_IntroToOptProblems
import CvxOpt._01_TypesOfMinimizers_IntroConvexity_pre


section main

variable
    {D: Type*}
    {R: Type*}

@[deprecated "just use `x ∈ C`" (since := "2025-03-27")]
def FeasiblePoint
    (C : Set D)
    (x : D)
    : Prop := x ∈ C

example
    [LE R] {C : Set D} {x : D}
    : FeasiblePoint C x ↔ x ∈ C
    := by rfl

@[deprecated "just use `x ∈ ArgumentMinimumOn f C`" (since := "2025-03-27")]
def GlobalMinimizer
    [LE R]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop := x ∈ C ∧ ∀ y ∈ C, f x ≤ f y

example
    [LE R] {f: D → R} {C : Set D} {x : D}
    : GlobalMinimizer f C x ↔ x ∈ ArgumentMinimumOn f C
    := by
    simp [GlobalMinimizer, ArgumentMinimumOn, MinimumOn, IsLeast, lowerBounds]
    intro xinC _
    constructor
    case left => exact xinC
    case right => exists x

def LocalMinimizer
    [PseudoMetricSpace D] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ ε : NNReal, ∀ y ∈ (C ∩ Metric.ball x ε), f x ≤ f y

def StrictLocalMinimizer
    [PseudoMetricSpace D] [LT R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ ε : NNReal, ∀ y ∈ (C ∩ Metric.ball x ε), f x < f y

def IsolatedStrictLocalMinimizer
    [PseudoMetricSpace D] [LT R] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    :=
        StrictLocalMinimizer f C x
        ∧ ∃ ε : NNReal, ∀ y : D, (LocalMinimizer f (C ∩ Metric.ball x ε) y → y = x)

end main
