import Stilt.Syntax

/-!
# The forms of projections and of writable views

Which forms of the calculus are those of projections (`Stilt.Projections`) and of writable views
(`Stilt.Writable`), each typed as the code it means (`HasType.form`).
-/

namespace Stilt

/-- The forms of projections, which typing checks as the calls each means (`HasType.form`). -/
def Form.ofProjection : Form → Bool
  | .projection | .yield | .yielded | .project => true
  | .letElse | .orElse | .writes | .through | .compound | .intFloat | .optionField | .update | .element => false
  | .spawn | .await | .scope | .scopeSpawn | .async | .lazyNew | .lazyGet => false
  | .parMap | .parEach | .parBoth | .parFold | .viewIndex | .iter _ | .traitConst _ | .proved _ => false

/-- The forms of writable views, which typing checks as the code each means (`HasType.form`) and
`Program.ViewsWrite` checks the rules of (`Stilt.Writable`). -/
def Form.ofWritable : Form → Bool
  | .writes | .through => true
  | .letElse | .orElse | .projection | .yield | .yielded | .project | .compound | .intFloat | .optionField | .update | .element => false
  | .spawn | .await | .scope | .scopeSpawn | .async | .lazyNew | .lazyGet => false
  | .parMap | .parEach | .parBoth | .parFold | .viewIndex | .iter _ | .traitConst _ | .proved _ => false

/-- The marks of operations that verification proves (`Stilt.Analysis`). -/
def Form.isProved : Form → Bool
  | .proved _ => true
  | _ => false

/-- The forms that typing checks as the code each means: those of projections, those of
writable views and the marks of proved operations (`HasType.form`). -/
def Form.meant (k : Form) : Bool := k.ofProjection || k.ofWritable || k.isProved

end Stilt
