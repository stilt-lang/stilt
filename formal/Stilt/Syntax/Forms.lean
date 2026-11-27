import Stilt.Syntax

/-!
# The forms of projections

Which forms of the calculus are those of projections (`Stilt.Projections`), each typed as the
calls it means (`HasType.form`).
-/

namespace Stilt

/-- The forms of projections, which typing checks as the calls each means (`HasType.form`). -/
def Form.ofProjection : Form → Bool
  | .projection | .yield | .yielded | .project => true
  | .letElse | .orElse => false

end Stilt
