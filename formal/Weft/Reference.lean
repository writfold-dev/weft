import Lean
import Weft

namespace Weft.Reference
open Lean Weft.Logic

/-- Test/reference protocol only; not Writfold RPC or an evidence admission path. -/
def decodeFormula : Nat → Json → Except String Formula
  | 0, _ => .error "formula nesting exceeds reference bound"
  | fuel + 1, value => do
      let kind ← (← value.getObjVal? "kind").getStr?
      match kind with
      | "atom" => return .atom (← (← value.getObjVal? "index").getNat?)
      | "literal" => return .literal (← (← value.getObjVal? "value").getBool?)
      | "not" => return .neg (← decodeFormula fuel (← value.getObjVal? "inner"))
      | "and" =>
          let left ← decodeFormula fuel (← value.getObjVal? "left")
          let right ← decodeFormula fuel (← value.getObjVal? "right")
          return .conj left right
      | "or" =>
          let left ← decodeFormula fuel (← value.getObjVal? "left")
          let right ← decodeFormula fuel (← value.getObjVal? "right")
          return .disj left right
      | _ => .error "unknown formula kind"

def verdictName : Verdict → String
  | .entailed => "entailed"
  | .refuted => "refuted"
  | .undetermined => "undetermined"
  | .inconsistent => "inconsistent-premises"
  | .unknown => "unknown"

def evaluateRequest (input : Json) : Except String Json := do
  let id ← (← input.getObjVal? "id").getStr?
  let atoms ← (← input.getObjVal? "atoms").getNat?
  let budget ← (← input.getObjVal? "budget").getNat?
  if atoms > 20 then throw "reference atom-domain bound exceeded"
  let rawPremises ← (← input.getObjVal? "premises").getArr?
  let premises ← rawPremises.toList.mapM (decodeFormula 256)
  let query ← decodeFormula 256 (← input.getObjVal? "query")
  return Json.mkObj [("id", .str id),
    ("verdict", .str (verdictName (classify atoms premises query budget)))]

def respond (line : String) : Json :=
  match Json.parse line >>= evaluateRequest with
  | .ok result => result
  | .error message => Json.mkObj [("error", .str message)]

end Weft.Reference

/-- Read a finite JSONL corpus and emit actual calculus outcomes. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let source ← IO.FS.readFile path
      let output ← IO.getStdout
      let mut failed := false
      for line in source.splitOn "\n" do
        if !line.trim.isEmpty then
          let result := Weft.Reference.respond line
          if (result.getObjVal? "error").isOk then failed := true
          output.putStrLn result.compress
      return if failed then 1 else 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: weftref CASES.jsonl (qualification reference only)"
      return 2
