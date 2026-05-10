import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.longLine false

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := Metric.sphere (0 : R3) 1

def IsDrawingEdge (e : Set S2) : Prop :=
  ∃ f : unitInterval ≃ₜ closure e, closure e \ e = {↑(f 0), ↑(f 1)}

structure Drawing where
  univ : Set S2
  univ_closed : IsClosed univ
  vertices : Finset S2
  vertices_in_univ : ↑vertices ⊆ univ
  edges_finite : Finite (ZerothHomotopy ↑(univ \ vertices))
  edges_are_line : ∀ x ∈ (univ \ vertices), IsDrawingEdge (pathComponentIn (univ \ vertices) x)

def Drawing.HasEdge (g : Drawing) (u v : g.vertices) :=
  ∃ x ∈ (g.univ \ g.vertices),
    let e := pathComponentIn (g.univ \ g.vertices) x
    closure e \ e = {↑u, ↑v}

def IsColoring (g : Drawing) (α : Type*) (f : g.vertices → α) :=
  ∀ u v : g.vertices, g.HasEdge u v → f u ≠ f v

theorem four_color_theorem (g : Drawing) : ∃ f, IsColoring g (Fin 4) f := by
  sorry
