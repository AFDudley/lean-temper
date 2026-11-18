/-
  Text edits (see ../README.md).

  `Edit` is a byte-range replacement in a file's current text. `applyEdits`
  takes a set of non-overlapping edits and applies them in one pass, last
  offset first, so that the offsets of the edits not yet applied stay valid.
-/
import Lean

open Lean

namespace LeanTemper

structure Edit where
  start : Nat
  stop : Nat
  replacement : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Apply non-overlapping edits, last offset first. -/
def applyEdits (text : String) (edits : Array Edit) : String := Id.run do
  let sorted := edits.qsort fun a b => a.start > b.start || (a.start == b.start && a.stop > b.stop)
  let mut t := text
  for e in sorted do
    t := String.Pos.Raw.extract t 0 ⟨e.start⟩ ++ e.replacement ++ String.Pos.Raw.extract t ⟨e.stop⟩ ⟨t.utf8ByteSize⟩
  return t

end LeanTemper
