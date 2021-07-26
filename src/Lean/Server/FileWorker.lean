/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Server.Utils
import Lean.Server.Snapshots
import Lean.Server.AsyncList

import Lean.Server.FileWorker.Utils
import Lean.Server.FileWorker.RequestHandling

/-!
For general server architecture, see `README.md`. For details of IPC communication, see `Watchdog.lean`.
This module implements per-file worker processes.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.

To achieve these goals, elaboration is executed in a chain of tasks, where each task corresponds to
the elaboration of one command. When the elaboration of one command is done, the next task is spawned.
On didChange notifications, we search for the task in which the change occured. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occured.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occured somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean.Server.FileWorker

open Lsp
open IO
open Snapshots
open Std (RBMap RBMap.empty)
open JsonRpc

/- Asynchronous snapshot elaboration. -/
section Elab
  /-- Elaborates the next command after `parentSnap` and emits diagnostics into `hOut`. -/
  private def nextCmdSnap (m : DocumentMeta) (parentSnap : Snapshot) (cancelTk : CancelToken) (hOut : FS.Stream)
      : ExceptT ElabTaskError IO Snapshot := do
    cancelTk.check
    publishProgressAtPos m parentSnap.endPos hOut
    let maybeSnap ← compileNextCmd m.text.source parentSnap
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
    match maybeSnap with
    | Sum.inl snap =>
      /- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
        while prefering newer versions over old ones. The former is necessary because we do
        not explicitly clear older diagnostics, while the latter is necessary because we do
        not guarantee that diagnostics are emitted in order. Specifically, it may happen that
        we interrupted this elaboration task right at this point and a newer elaboration task
        emits diagnostics, after which we emit old diagnostics because we did not yet detect
        the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
        because we cannot guarantee that no further diagnostics are emitted after clearing
        them. -/
      if snap.msgLog.msgs.size > parentSnap.msgLog.msgs.size then
        publishMessages m snap.msgLog hOut
      snap
    | Sum.inr msgLog =>
      publishMessages m msgLog hOut
      publishProgressDone m hOut
      throw ElabTaskError.eof

  /-- Elaborates all commands after `initSnap`, emitting the diagnostics into `hOut`. -/
  def unfoldCmdSnaps (m : DocumentMeta) (initSnap : Snapshot) (cancelTk : CancelToken) (hOut : FS.Stream)
    (initial : Bool) :
      IO (AsyncList ElabTaskError Snapshot) := do
    if initial && initSnap.msgLog.hasErrors then
      -- treat header processing errors as fatal so users aren't swamped with followup errors
      AsyncList.nil
    else
      AsyncList.unfoldAsync (nextCmdSnap m . cancelTk hOut) initSnap
end Elab

-- Pending requests are tracked so they can be cancelled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure WorkerContext where
  hIn           : FS.Stream
  hOut          : FS.Stream
  hLog          : FS.Stream
  srcSearchPath : SearchPath

structure WorkerState where
  doc             : EditableDocument
  pendingRequests : PendingRequestMap
  rpcSesh         : Option RpcSession

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/- Worker initialization sequence. -/
section Initialization
  /-- Use `leanpkg print-paths` to compile dependencies on the fly and add them to `LEAN_PATH`.
  Compilation progress is reported to `hOut` via LSP notifications. Return the search path for
  source files. -/
  partial def leanpkgSetupSearchPath (leanpkgPath : System.FilePath) (m : DocumentMeta) (imports : Array Import) (hOut : FS.Stream) : IO SearchPath := do
    let leanpkgProc ← Process.spawn {
      stdin  := Process.Stdio.null
      stdout := Process.Stdio.piped
      stderr := Process.Stdio.piped
      cmd    := leanpkgPath.toString
      args   := #["print-paths"] ++ imports.map (toString ·.module)
    }
    -- progress notification: report latest stderr line
    let rec processStderr (acc : String) : IO String := do
      let line ← leanpkgProc.stderr.getLine
      if line == "" then
        return acc
      else
        publishDiagnostics m #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.information, message := line }] hOut
        processStderr (acc ++ line)
    let stderr ← IO.asTask (processStderr "") Task.Priority.dedicated
    let stdout := String.trim (← leanpkgProc.stdout.readToEnd)
    let stderr ← IO.ofExcept stderr.get
    if (← leanpkgProc.wait) == 0 then
      let leanpkgLines := stdout.split (· == '\n')
      -- ignore any output up to the last two lines
      -- TODO: leanpkg should instead redirect nested stdout output to stderr
      let leanpkgLines := leanpkgLines.drop (leanpkgLines.length - 2)
      match leanpkgLines with
      | [""]                    => pure []  -- e.g. no leanpkg.toml
      | [leanPath, leanSrcPath] => let sp ← getBuiltinSearchPath
                                   let sp ← addSearchPathFromEnv sp
                                   let sp := System.SearchPath.parse leanPath ++ sp
                                   searchPathRef.set sp
                                   let srcPath := System.SearchPath.parse leanSrcPath
                                   srcPath.mapM realPathNormalized
      | _                       => throwServerError s!"unexpected output from `leanpkg print-paths`:\n{stdout}\nstderr:\n{stderr}"
    else
      throwServerError s!"`leanpkg print-paths` failed:\n{stdout}\nstderr:\n{stderr}"

  def compileHeader (m : DocumentMeta) (hOut : FS.Stream) : IO (Snapshot × SearchPath) := do
    let opts := {}  -- TODO
    let inputCtx := Parser.mkInputContext m.text.source "<input>"
    let (headerStx, headerParserState, msgLog) ← Parser.parseHeader inputCtx
    let leanpkgPath ← match (← IO.getEnv "LEAN_SYSROOT") with
      | some path => pure <| System.FilePath.mk path / "bin" / "leanpkg"
      | _         => pure <| (← appDir) / "leanpkg"
    let leanpkgPath := leanpkgPath.withExtension System.FilePath.exeExtension
    let mut srcSearchPath := [(← appDir) / ".." / "lib" / "lean" / "src"]
    if let some p := (← IO.getEnv "LEAN_SRC_PATH") then
      srcSearchPath := srcSearchPath ++ System.SearchPath.parse p
    let (headerEnv, msgLog) ← try
      -- NOTE: leanpkg does not exist in stage 0 (yet?)
      if (← System.FilePath.pathExists leanpkgPath) then
        let pkgSearchPath ← leanpkgSetupSearchPath leanpkgPath m (Lean.Elab.headerToImports headerStx).toArray hOut
        srcSearchPath := srcSearchPath ++ pkgSearchPath
      Elab.processHeader headerStx opts msgLog inputCtx
    catch e =>  -- should be from `leanpkg print-paths`
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := e.toString }
      pure (← mkEmptyEnvironment, msgs)
    publishMessages m msgLog hOut
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    let cmdState := { cmdState with infoState.enabled := true, scopes := [{ header := "", opts := opts }] }
    let headerSnap := {
      beginPos := 0
      stx := headerStx
      mpState := headerParserState
      cmdState := cmdState
    }
    return (headerSnap, srcSearchPath)

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream)
      : IO (WorkerContext × WorkerState) := do
    /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
      "\n", which should be enough to handle both LF and CRLF correctly.
      This is because LSP always refers to characters by (line, column),
      so if we get the line number correct it shouldn't matter that there
      is a CR there. -/
    let (headerSnap, srcSearchPath) ← compileHeader meta o
    let cancelTk ← CancelToken.new
    let cmdSnaps ← unfoldCmdSnaps meta headerSnap cancelTk o (initial := true)
    let doc : EditableDocument := ⟨meta, headerSnap, cmdSnaps, cancelTk⟩
    return ({
      hIn                := i
      hOut               := o
      hLog               := e
      srcSearchPath      := srcSearchPath
    },
    {
      doc             := doc
      pendingRequests := RBMap.empty
      rpcSesh         := none
    })
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  /-- Given the new document and `changePos`, the UTF-8 offset of a change into the pre-change source,
      updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) (changePos : String.Pos) : WorkerM Unit := do
    -- The watchdog only restarts the file worker when the syntax tree of the header changes.
    -- If e.g. a newline is deleted, it will not restart this file worker, but we still
    -- need to reparse the header so that the offsets are correct.
    let ctx ← read
    let oldDoc := (←get).doc
    let newHeaderSnap ← reparseHeader newMeta.text.source oldDoc.headerSnap
    if newHeaderSnap.stx != oldDoc.headerSnap.stx then
      throwServerError "Internal server error: header changed but worker wasn't restarted."
    let ⟨cmdSnaps, e?⟩ ← oldDoc.cmdSnaps.updateFinishedPrefix
    match e? with
    -- This case should not be possible. only the main task aborts tasks and ensures that aborted tasks
    -- do not show up in `snapshots` of an EditableDocument.
    | some ElabTaskError.aborted =>
      throwServerError "Internal server error: elab task was aborted while still in use."
    | some (ElabTaskError.ioError ioError) => throw ioError
    | _ => -- No error or EOF
      oldDoc.cancelTk.set
      -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
      -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
      let mut validSnaps := cmdSnaps.finishedPrefix.takeWhile (fun s => s.endPos < changePos)
      if validSnaps.length = 0 then
        let cancelTk ← CancelToken.new
        let newCmdSnaps ← unfoldCmdSnaps newMeta newHeaderSnap cancelTk ctx.hOut (initial := true)
        modify fun st => { st with doc := ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩ }
      else
        /- When at least one valid non-header snap exists, it may happen that a change does not fall
           within the syntactic range of that last snap but still modifies it by appending tokens.
           We check for this here. We do not currently handle crazy grammars in which an appended
           token can merge two or more previous commands into one. To do so would require reparsing
           the entire file. -/
        let mut lastSnap := validSnaps.getLast!
        let preLastSnap :=
          if validSnaps.length ≥ 2
          then validSnaps.get! (validSnaps.length - 2)
          else newHeaderSnap
        let newLastStx ← parseNextCmd newMeta.text.source preLastSnap
        if newLastStx != lastSnap.stx then
          validSnaps ← validSnaps.dropLast
          lastSnap ← preLastSnap
        let cancelTk ← CancelToken.new
        let newSnaps ← unfoldCmdSnaps newMeta lastSnap cancelTk ctx.hOut (initial := false)
        let newCmdSnaps := AsyncList.ofList validSnaps ++ newSnaps
        modify fun st => { st with doc := ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩ }
end Updates

/- Notifications are handled in the main thread. They may change global worker state
such as the current file contents. -/
section NotificationHandling
  def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc := (←get).doc
    let some newVersion ← pure docId.version?
      | throwServerError "Expected version number"
    if newVersion ≤ oldDoc.meta.version then
      -- TODO(WN): This happens on restart sometimes.
      IO.eprintln s!"Got outdated version number: {newVersion} ≤ {oldDoc.meta.version}"
    else if ¬ changes.isEmpty then
      let (newDocText, minStartOff) := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText⟩ minStartOff

  def handleCancelRequest (p : CancelParams) : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

  def handleRpcConnect (p : RpcConnectParams) : WorkerM Unit := do
    let ctx ← read
    let doc := (←get).doc
    /- We generate a random ID to ensure that session IDs do not repeat across re-initializations
    and worker restarts. Otherwise, the client may attempt to use outdated references. -/
    let newId ← ByteArray.toUInt64LE! <$> IO.getRandomBytes 8
    let newRpcState ← IO.mkRef {
      aliveRefs := Std.PersistentHashMap.empty
      nextRef := 0
    }
    /- Just setting this should `dec` the previous session. Any associated references
    will then no longer be kept alive for the client. -/
    modify fun st => { st with rpcSesh := some { sessionId := newId, state := newRpcState } }
    ctx.hOut.writeLspNotification
      <| { method := "$/lean/rpc/connected"
           param := { uri := doc.meta.uri
                      sessionId := newId : RpcConnected } }

def handleRpcRelease (p : Lsp.RpcReleaseParams) : WorkerM Unit := do
  let st ← get
  let some rpcSesh ← st.rpcSesh
    | throwServerError "TODO"
  if p.sessionId ≠ rpcSesh.sessionId then
    -- TODO(WN): should only print on log-level debug, if we had log-levels
    IO.eprintln s!"Trying to release ref '{p.ref}' from outdated RPC session '{p.sessionId}'."
  else
    rpcSesh.state.modify fun st => st.release p.ref

end NotificationHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : WorkerM paramType :=
    match fromJson? params with
    | Except.ok parsed => pure parsed
    | Except.error inner => throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

  def handleNotification (method : String) (params : Json) : WorkerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | "$/lean/rpc/connect"     => handle RpcConnectParams handleRpcConnect
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

  def queueRequest (id : RequestID) (requestTask : Task (Except IO.Error Unit))
      : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

  def handleRequest (id : RequestID) (method : String) (params : Json)
      : WorkerM Unit := do
    let ctx ← read
    let st ← get
    let rc : RequestContext :=
      { rpcSesh? := st.rpcSesh
        srcSearchPath := ctx.srcSearchPath
        doc := st.doc
        hLog := ctx.hLog }
    let t? ← (ExceptT.run <| handleLspRequest method params rc : IO _)
    let t₁ ← match t? with
      | Except.error e =>
        IO.asTask do
          ctx.hOut.writeLspResponseError <| e.toLspResponseError id
      | Except.ok t => (IO.mapTask · t) fun
        | Except.ok resp =>
          ctx.hOut.writeLspResponse ⟨id, resp⟩
        | Except.error e =>
          ctx.hOut.writeLspResponseError <| e.toLspResponseError id
    queueRequest id t₁
end MessageHandling

section MainLoop
  partial def mainLoop : WorkerM Unit := do
    let ctx ← read
    let msg ← ctx.hIn.readLspMessage
    let pendingRequests := (←get).pendingRequests
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : WorkerM PendingRequestMap := do
      if (←hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        acc.erase id
      else acc
    let pendingRequests ← pendingRequests.foldM filterFinishedTasks pendingRequests
    modify fun st => { st with pendingRequests := pendingRequests }
    match msg with
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      mainLoop
    | Message.notification "exit" none =>
      let doc ← (←get).doc
      doc.cancelTk.set
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let _ ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let doc := param.textDocument
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap⟩
  let e ← e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let (ctx, st) ← initializeWorker meta i o e
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) mainLoop
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
    return (1 : UInt32)

@[export lean_server_worker_main]
def workerMain : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let exitCode ← initAndRunWorker i o e
    -- HACK: all `Task`s are currently "foreground", i.e. we join on them on main thread exit, but we definitely don't
    -- want to do that in the case of the worker processes, which can produce non-terminating tasks evaluating user code
    o.flush
    e.flush
    IO.Process.exit exitCode.toUInt8
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return (1 : UInt32)

end Lean.Server.FileWorker
