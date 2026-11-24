import Stilt.Windows.Relation
import Stilt.InPlace.Agreement

/-!
# The functions the checks of views accept

What a call needs of the function it calls: its parameters named once each, its body's closure
literals too, its body obeying the law and accepted by both checks of views in the scope of its
parameters. A well-typed program that obeys the law and whose checks of views accept it gives
every function that.
-/

namespace Stilt

namespace Windows

/-- Every function of `D` names its parameters once, and so do its body's closure literals,
its body obeys the law of exclusivity, and the checks of views accept its body in the scope of
its parameters, with the result's parameters the value it gives may read (views.across-calls). -/
def DeclsChecked (D : Decls) : Prop :=
  ∀ d ∈ D.fns, (d.params.map Param.name).Nodup ∧ d.body.distinctParams = true ∧
    d.body.exclusive [] = true ∧ d.body.viewsRead D (d.viewScope D) [] = true ∧
    d.body.contained D (d.viewScope D) (resultParams D d.params d.result) = true ∧
    leaves (resultParams D d.params d.result) (d.body.sources D (d.viewScope D)) = true

/-- A well-typed program that obeys the law and whose checks of views accept it has its
functions checked. -/
theorem declsChecked_of {p : Program} (hwt : p.WellTyped) (hex : p.Exclusive)
    (hr : p.ViewsRead) (hc : p.ViewsContained) : DeclsChecked p.decls := fun d hd => by
  obtain ⟨σ, hty, -⟩ := hwt.typedIn.fns d hd
  exact ⟨hwt.decls.paramNames d hd, hty.distinctParams, hex.1 d hd, hr.1 d hd, (hc.1 d hd).1,
    (hc.1 d hd).2⟩

/-- A well-typed program's `main` names the parameters of its closure literals once. -/
theorem main_distinctParams {p : Program} (hwt : p.WellTyped) : p.main.distinctParams = true := by
  obtain ⟨σ, hty, -⟩ := hwt.main
  exact hty.distinctParams

end Windows

end Stilt
