import Lean
import Silean2.Modules.RegistryH
import Silean2.CIRCT.RegistryH
import Silean2.FoundationsH

namespace Silean2.CIRCT

open Silean2.Foundations
open Silean2

structure BuildConfig where
  mod : String
  params : Lean.Json
  settings : CIRCTSettings
  deriving Lean.FromJson

def fieldNames : RawParamsFields → List String
  | .nil => []
  | .cons name _ rest => name :: fieldNames rest

mutual
  def decodeParams (type : RawParamsType) (value : Lean.Json) (path : String) :
      Except String type.Denote :=
    match type with
      | .nat => value.getNat?.mapError (fun message => s!"{path}: {message}")
      | .bool => value.getBool?.mapError (fun message => s!"{path}: {message}")
      | .vector element length => do
        let entries ← value.getArr?.mapError (fun message => s!"{path}: {message}")
        if h : entries.size = length then
          let entries : Vector Lean.Json length := ⟨entries, h⟩
          let decoded ← collect fun i : Fin length =>
            decodeParams element entries[i] s!"{path}[{i.val}]"
          return Vector.ofFn decoded
        else
          throw s!"{path}: Vector expected length is {length} does not match seen length of {entries.size}"
      | .record fields => do
          let object ← value.getObj?.mapError (fun message => s!"{path}: {message}")
          let mut names : Std.HashSet String := {}
          for name in fieldNames fields do
            if !names.contains name then
              throw s!"{path}: duplicate field {name} in parameter schema"
            names := names.insert name
          for (name, _) in object.toList do
            if !name.contains name then do
              throw s!"{path}: Unknown field: {name}"
          decodeFields fields value path

  def decodeFields (fields : RawParamsFields) (object : Lean.Json) (path : String) :
      Except String fields.Denote :=
    match fields with
      | .nil => pure ()
      | .cons name type rest => do
        let value ← (object.getObjVal? name).mapError (fun _ => s!"{path}.{name}: missing field")
        let decoded ← decodeParams type value s!"{path}.{name}"
        let remaining ← decodeFields rest object path
        return (decoded, remaining)
end

def emitJson (source : String) : Except String String := do
  let json ← Lean.Json.parse source
  let config : BuildConfig ← Lean.fromJson? json
  -- Need to use a match here because registry is Type 1 and that means
  -- the except Monads don't play nicely.
  match Modules.registry with
  | .error message => .error message
  | .ok thisRegistry => do
    let some registration := thisRegistry[config.mod]? | throw s!"Module {config.mod} not found in registry"
    let rawParams ← decodeParams registration.rawParamsType config.params "params"
    let params ← registration.decodeParams rawParams
    let top : ModuleRef (registration.ports params) := {
      name := config.mod,
      paramsType := registration.rawParamsType,
      params := rawParams,
    }
    let modules ← buildDesign config.settings thisRegistry top

    let mut output := "module {\n"
    for mod in modules do
      output := output ++ (← emitModule mod.2)
    return output ++ "}\n"

end Silean2.CIRCT

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    try
      let source ← IO.FS.readFile file
      match Silean2.CIRCT.emitJson source with
      | .ok mlir =>
        (← IO.getStdout).putStr mlir
        return 0
      | .error message =>
        (← IO.getStderr).putStrLn message
        return 1
    catch error =>
      (← IO.getStderr).putStrLn s!"error: {error}"
      return 1
  | _ =>
    (← IO.getStderr).putStrLn "Usage: emit-circt config.json"
    return 1
