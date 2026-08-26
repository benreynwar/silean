import Silean2.FIRRTL.Render

namespace Silean2.FIRRTL

private def usage (executableName : String) : String :=
  s!"usage: {executableName} [--output PATH]"

def emitMain (executableName : String) (args : List String)
    (rendered : RenderResult String) : IO Unit := do
  let text ← match rendered with
    | .ok text => pure text
    | .error message => throw <| IO.userError s!"FIRRTL rendering failed: {message}"
  match args with
  | [] => IO.print text
  | ["--output", path] => IO.FS.writeFile path text
  | _ => throw <| IO.userError (usage executableName)

end Silean2.FIRRTL
