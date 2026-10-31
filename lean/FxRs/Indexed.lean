import FxRs.Laws

/-!
Indexed kernel `IFx S1 S2 V`: a computation that needs context `S1` and
ends with context `S2`. Atkey's typed state
`T (S1, S2, A) = (S2 × A)^S1` (Atkey, "Parameterised Notions of Computation", JFP 2009).

`adapt` keeps the body of `kernel/fx.rs:44-49`. Only the types change.
`contraMap` takes a heterogeneous lens `(T1, T2) ⇸ (S1, S2)`, the lens of
Wilshaw and Hutton, "Flow Typing: A New Lens on Linearity", Def. 3.2.
-/

namespace FxRs

inductive IFx (S1 S2 V : Type) where
  | immediate : S2 → V → IFx S1 S2 V
  | pending : (S1 → IFx S1 S2 V) → IFx S1 S2 V

namespace IFx

variable {S1 S2 S3 T1 T2 V U W : Type}

def adapt (cmap : T1 → S1) (fmap : T1 → S2 → V → IFx T1 T2 U) :
    IFx S1 S2 V → IFx T1 T2 U
  | immediate s v => pending fun t => fmap t s v
  | pending f => pending fun t => adapt cmap fmap (f (cmap t))

/-- Runs only when no context is needed and none is left. -/
def eval : IFx Unit Unit V → V
  | immediate _ v => v
  | pending f => eval (f ())

def run : IFx S1 S2 V → S1 → S2 × V
  | immediate s v, _ => (s, v)
  | pending f, s => run (f s) s

def value (v : V) : IFx S S V := pending fun s => immediate s v

def contraMap (get : T1 → S1) (set : T1 → S2 → T2) (e : IFx S1 S2 V) : IFx T1 T2 V :=
  e.adapt get fun t s v => immediate (set t s) v

/-- Indexed bind: the post-context of `e` is the pre-context of `f v`. -/
def mapM (f : V → IFx S2 S3 U) (e : IFx S1 S2 V) : IFx S1 S3 U :=
  e.adapt id fun _ s v => (f v).contraMap (fun _ => s) fun _ s => s

theorem run_adapt (cmap : T1 → S1) (fmap : T1 → S2 → V → IFx T1 T2 U)
    (e : IFx S1 S2 V) (t : T1) :
    run (e.adapt cmap fmap) t = run (fmap t (run e (cmap t)).1 (run e (cmap t)).2) t := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => exact ih (cmap t)

theorem run_value (v : V) (s : S1) : run (value v) s = (s, v) := rfl

theorem run_contraMap (get : T1 → S1) (set : T1 → S2 → T2) (e : IFx S1 S2 V) (t : T1) :
    run (e.contraMap get set) t = (set t (run e (get t)).1, (run e (get t)).2) := by
  simp only [contraMap, run_adapt]; rfl

theorem run_mapM (f : V → IFx S2 S3 U) (e : IFx S1 S2 V) (s : S1) :
    run (e.mapM f) s = run (f (run e s).2) (run e s).1 := by
  simp only [mapM, run_adapt, run_contraMap]; rfl

def Equiv (e e' : IFx S1 S2 V) : Prop := ∀ s, run e s = run e' s

infix:50 " ≈ " => Equiv

theorem mapM_left_id (v : V) (f : V → IFx S1 S2 U) : (value v).mapM f ≈ f v := by
  intro s; simp only [run_mapM, run_value]

theorem mapM_right_id (e : IFx S1 S2 V) : e.mapM value ≈ e := by
  intro s; simp only [run_mapM, run_value]

theorem mapM_assoc {S4 : Type} (e : IFx S1 S2 V) (f : V → IFx S2 S3 U)
    (g : U → IFx S3 S4 W) :
    (e.mapM f).mapM g ≈ e.mapM fun v => (f v).mapM g := by
  intro s; simp only [run_mapM]

/-! ### Embedding of the current kernel: `Fx S V ≅ IFx S S V` -/

def ofFx : Fx S V → IFx S S V
  | .immediate s v => immediate s v
  | .pending f => pending fun s => ofFx (f s)

def toFx : IFx S S V → Fx S V
  | immediate s v => .immediate s v
  | pending f => .pending fun s => toFx (f s)

theorem toFx_ofFx (e : Fx S V) : toFx (ofFx e) = e := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => simp only [ofFx, toFx, ih]

theorem ofFx_toFx (e : IFx S S V) : ofFx (toFx e) = e := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => simp only [ofFx, toFx, ih]

/-- `adapt` of the current kernel is `adapt` of the indexed kernel. -/
theorem ofFx_adapt {S T V U : Type} (cmap : T → S) (fmap : T → S → V → Fx T U) (e : Fx S V) :
    ofFx (e.adapt cmap fmap) = (ofFx e).adapt cmap fun t s v => ofFx (fmap t s v) := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => simp only [Fx.adapt, adapt, ofFx, ih]

theorem run_ofFx {S V : Type} (e : Fx S V) (s : S) : run (ofFx e) s = e.run s := by
  induction e generalizing s with
  | immediate _ _ => rfl
  | pending f ih => exact ih s s

end IFx

/-! ### Typestate example: a door that must be opened before it is closed -/

namespace DoorExample
open IFx

structure Closed where
structure Opened where

def openDoor : IFx Closed Opened Unit := pending fun _ => immediate ⟨⟩ ()
def closeDoor : IFx Opened Closed Unit := pending fun _ => immediate ⟨⟩ ()

def session : IFx Closed Closed Unit := openDoor.mapM fun _ => closeDoor

example : (session.run ⟨⟩).2 = () := rfl

-- Negative control: closing a closed door does not type-check.
#check_failure (closeDoor.mapM fun _ => closeDoor)

-- Negative control: a session that leaves the door open cannot run.
#check_failure (openDoor.contraMap (fun (_ : Unit) => Closed.mk) (fun _ s => s)).eval

end DoorExample

end FxRs
