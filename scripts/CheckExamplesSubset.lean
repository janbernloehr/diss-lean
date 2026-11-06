import Lean

open Lean Elab Frontend

namespace CheckExamplesSubset

-- Use Lean's normal parser and command elaborator, retaining all nonexample
-- commands. Unchanged anonymous examples already passed the full run and do
-- not change the environment (Lean.Elab.MutualDef.elabMutualDef).
def exampleNodes (stx : Syntax) : Array Syntax := Id.run do
  let mut pending := #[stx]
  let mut found := #[]
  while !pending.isEmpty do
    let node := pending.back!
    pending := pending.pop
    if node.isOfKind ``Parser.Command.example then
      found := found.push node
    else
      pending := pending ++ node.getArgs.reverse
  return found

def checkStep (lines : Array Nat) (counts : IO.Ref (Nat × Nat)) : FrontendM Bool := do
  updateCmdPos
  let state ← getCommandState
  let input ← getInputContext
  let parser ← getParserState
  let scope := state.scopes.head!
  let context := { env := state.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (command,parser,messages) := Parser.parseCommand input context parser state.messages
  setParserState parser
  setMessages messages
  let isExample := command.isOfKind ``Parser.Command.declaration &&
    command[1].isOfKind ``Parser.Command.example
  let nodes := if isExample then #[command[1]] else exampleNodes command
  let mut selected := false
  for node in nodes do
    let (total,checked) ← counts.get
    let index := total+1
    let position := input.fileMap.toPosition (node.getPos?.getD 0)
    let chosen := lines.contains position.line
    counts.set (index,checked+(if chosen then 1 else 0))
    if chosen then
      selected := true
      IO.println s!"Rechecking example #{index} at source line {position.line}"
  if selected || !isExample then
    elabCommandAtFrontend command
  return Parser.isTerminalCommand command

end CheckExamplesSubset

def main (args : List String) : IO UInt32 := do
  let [file,lineList,expectedText] := args
    | throw <| IO.userError "Expected source file, comma-separated source lines, total example count"
  let selectedLines := (lineList.splitOn ",").filterMap String.toNat? |>.toArray
  let some expected := expectedText.toNat? | throw <| IO.userError "Invalid count"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile file
  let context := Parser.mkInputContext input file
  let (header,parser,messages) ← Parser.parseHeader context
  let options := (({} : Options).setBool `autoImplicit false).setBool `warningAsError true
  let (env,messages) ← processHeader header options messages context
    (mainModule := `scripts.CheckExamples)
  let mut state : Frontend.State := {
    commandState := Command.mkState env messages options,
    parserState := parser, cmdPos := parser.pos }
  let counts ← IO.mkRef (0,0)
  repeat
    let (done,next) ← ((CheckExamplesSubset.checkStep selectedLines counts).run { inputCtx := context }).run state
    state := next
    if done then break
  let (total,checked) ← counts.get
  for message in state.commandState.messages.toList do
    IO.println (← message.toString)
  unless total==expected && checked==selectedLines.size do
    throw <| IO.userError s!"Coverage mismatch: {total} traversed, {checked} checked"
  if state.commandState.messages.toList.any (fun m => m.severity != .information) then
    return 1
  IO.println s!"Original-context example recheck passed: {total} traversed, {checked} corrected examples checked normally"
  return 0
