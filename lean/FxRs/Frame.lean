import FxRs.Indexed

/-!
Frame rule for the indexed kernel.

An `Optic` is a representative `⟨l | r⟩` of Riley's
`Optic((S, S'), (A, A')) := ∫^M C(S, M ⊗ A) × C(M ⊗ A', S')`
(`vic/papers/riley-optics.txt:178-186`), with the residual `R` explicit.
The residual holds the rest of the context. `zoom` passes it through
unchanged, so a framed step cannot write to the rest of the context.

`zoom_mapM` is Brady's `call` (`vic/papers/brady-st.txt:466-471`): a
subprogram typed against a small context runs in a larger one, and the
parent context is rebuilt after it.
-/

namespace FxRs

structure Optic (O1 O2 I1 I2 R : Type) where
  fwd : O1 → I1 × R
  bwd : I2 × R → O2

namespace IFx

variable {O1 O2 O3 I1 I2 I3 R V U : Type}

/-- Runs `e` on the focus of the context. -/
def zoom (l : Optic O1 O2 I1 I2 R) (e : IFx I1 I2 V) : IFx O1 O2 V :=
  e.contraMap (fun o => (l.fwd o).1) fun o i => l.bwd (i, (l.fwd o).2)

theorem run_zoom (l : Optic O1 O2 I1 I2 R) (e : IFx I1 I2 V) (o : O1) :
    run (zoom l e) o =
      (l.bwd ((run e (l.fwd o).1).1, (l.fwd o).2), (run e (l.fwd o).1).2) := by
  simp only [zoom, run_contraMap]

/-- The residual is not changed by the framed step. -/
theorem zoom_frame (l : Optic O1 O2 I1 I2 R) (e : IFx I1 I2 V) (o : O1) :
    (run (zoom l e) o).1 = l.bwd ((run e (l.fwd o).1).1, (l.fwd o).2) := by
  simp only [run_zoom]

/-- Framing commutes with indexed bind. `h`: rebuilding the middle context
and focusing it again gives back the same focus and residual. -/
theorem zoom_mapM (l : Optic O1 O2 I1 I2 R) (l' : Optic O2 O3 I2 I3 R)
    (h : ∀ x, l'.fwd (l.bwd x) = x) (e : IFx I1 I2 V) (f : V → IFx I2 I3 U) :
    zoom ⟨l.fwd, l'.bwd⟩ (e.mapM f) ≈ (zoom l e).mapM fun v => zoom l' (f v) := by
  intro o; simp only [run_zoom, run_mapM, h]

/-- The product frame: the first component is the focus. -/
def first : Optic (A × R) (B × R) A B R := ⟨id, id⟩

theorem first_fwd_bwd {A B C : Type} (x : B × R) :
    (first : Optic (B × R) (C × R) B C R).fwd ((first : Optic (A × R) (B × R) A B R).bwd x) = x :=
  rfl

end IFx

namespace FrameExample
open IFx DoorExample

/-- The door session runs inside a larger context. The log is not changed. -/
example :
    run (zoom IFx.first session) (Closed.mk, "log") = ((Closed.mk, "log"), ()) := rfl

-- Negative control: a framed step that ends with the door open does not
-- give a context with a closed door.
#check_failure (zoom IFx.first openDoor : IFx (Closed × String) (Closed × String) Unit)

end FrameExample

end FxRs
