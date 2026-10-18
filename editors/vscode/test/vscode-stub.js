// A stub of the part of the VS Code API the extension uses, so that the compiled extension runs
// under plain node: test/extension.test.ts drives it with stand-ins for cargo, and
// test/drive-real.js with a real thrust-rustc. `__state` holds what the extension did:
// diagnostics by file, the test runs with each item's states, the items it invalidated, the
// registered commands, providers and save handler, the warnings shown; and the open documents.
const fs = require("fs");

const state = {};

function reset() {
  Object.assign(state, {
    commands: {},
    diagnostics: new Map(),
    providers: {},
    runs: [],
    config: {},
    folder: "",
    status: {},
    warnings: [],
    log: "",
    controller: undefined,
    profile: undefined,
    documents: new Map(),
    invalidated: [],
    onSave: undefined,
  });
}
reset();

class Uri {
  constructor(fsPath) {
    this.scheme = "file";
    this.fsPath = fsPath;
  }
  static file(fsPath) {
    return new Uri(fsPath);
  }
  static parse(text) {
    return new Uri(text.replace(/^file:\/\//, ""));
  }
  toString() {
    return `file://${this.fsPath}`;
  }
}

class Position {
  constructor(line, character) {
    this.line = line;
    this.character = character;
  }
}

class Range {
  constructor(startLine, startCharacter, endLine, endCharacter) {
    this.start = new Position(startLine, startCharacter);
    this.end = new Position(endLine, endCharacter);
  }
}

class Location {
  constructor(uri, range) {
    this.uri = uri;
    this.range = range;
  }
}

class Diagnostic {
  constructor(range, message, severity) {
    this.range = range;
    this.message = message;
    this.severity = severity;
  }
}

class DiagnosticRelatedInformation {
  constructor(location, message) {
    this.location = location;
    this.message = message;
  }
}

class EventEmitter {
  constructor() {
    this.event = () => ({ dispose() {} });
  }
  fire() {}
  dispose() {}
}

class InlayHint {
  constructor(position, label) {
    this.position = position;
    this.label = label;
  }
}

class MarkdownString {
  constructor() {
    this.value = "";
  }
  appendCodeblock(text) {
    this.value += text;
    return this;
  }
}

class Hover {
  constructor(contents) {
    this.contents = contents;
  }
}

class CodeLens {
  constructor(range, command) {
    this.range = range;
    this.command = command;
  }
}

class TestMessage {
  constructor(message) {
    this.message = message;
  }
}

class TestRunRequest {
  constructor(include) {
    this.include = include;
  }
}

/// A TestItemCollection: children of `owner` (undefined for the controller's roots).
function collection(owner) {
  const map = new Map();
  return {
    add(item) {
      item.parent = owner;
      map.set(item.id, item);
    },
    get(id) {
      return map.get(id);
    },
    replace(list) {
      map.clear();
      list.forEach((item) => this.add(item));
    },
    delete(id) {
      map.delete(id);
    },
    forEach(f) {
      [...map.values()].forEach((item) => f(item));
    },
    get size() {
      return map.size;
    },
  };
}

function createTestItem(id, label, uri) {
  const item = { id, label, uri, range: undefined, parent: undefined };
  item.children = collection(item);
  return item;
}

function createTestRun(request) {
  const run = { request, states: [], ended: false };
  for (const name of ["started", "passed", "failed", "errored", "skipped"]) {
    run[name] = (item, messages) => {
      const list = messages === undefined ? [] : Array.isArray(messages) ? messages : [messages];
      run.states.push({ state: name, id: item.id, messages: list.map((m) => m.message) });
    };
  }
  run.end = () => (run.ended = true);
  state.runs.push(run);
  return run;
}

/// The open text document of the file on disk, opened at its first use; `dirty` makes it one
/// with unsaved changes. `version` counts edits, as `__edit` makes one.
function document(file, dirty) {
  const open = state.documents.get(file);
  if (open) {
    open.isDirty = dirty ?? open.isDirty;
    return open;
  }
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const opened = {
    uri: Uri.file(file),
    languageId: "rust",
    isDirty: dirty ?? false,
    version: 1,
    getText: () => text,
    lineCount: lines.length,
    lineAt: (line) => ({ range: { end: new Position(line, lines[line].length) } }),
  };
  state.documents.set(file, opened);
  return opened;
}

function edit(file) {
  const opened = document(file);
  opened.version += 1;
  opened.isDirty = true;
}

module.exports = {
  __state: state,
  __reset: reset,
  __document: document,
  __edit: edit,
  Uri,
  Position,
  Range,
  Location,
  Diagnostic,
  DiagnosticRelatedInformation,
  EventEmitter,
  InlayHint,
  MarkdownString,
  Hover,
  CodeLens,
  TestMessage,
  TestRunRequest,
  DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2 },
  StatusBarAlignment: { Left: 1 },
  TestRunProfileKind: { Run: 1 },
  window: {
    createOutputChannel: () => ({ appendLine: (line) => (state.log += `${line}\n`), show() {}, dispose() {} }),
    createStatusBarItem: () => Object.assign(state.status, { show() {}, dispose() {} }),
    showWarningMessage: (message) => state.warnings.push(message),
  },
  languages: {
    createDiagnosticCollection: () => ({
      clear: () => state.diagnostics.clear(),
      set: (uri, list) => state.diagnostics.set(uri.fsPath, list),
      get: (uri) => state.diagnostics.get(uri.fsPath),
      delete: (uri) => state.diagnostics.delete(uri.fsPath),
      dispose() {},
    }),
    registerInlayHintsProvider: (selector, provider) => (state.providers.hints = provider),
    registerHoverProvider: (selector, provider) => (state.providers.hover = provider),
    registerCodeLensProvider: (selector, provider) => (state.providers.lens = provider),
  },
  workspace: {
    getConfiguration: () => ({ get: (key, fallback) => (key in state.config ? state.config[key] : fallback) }),
    getWorkspaceFolder: () => ({ uri: Uri.file(state.folder) }),
    openTextDocument: async (uri) => document(uri.fsPath),
    get textDocuments() {
      return [...state.documents.values()];
    },
    onDidSaveTextDocument: (handler) => {
      state.onSave = handler;
      return { dispose() {} };
    },
  },
  commands: {
    registerCommand: (name, f) => {
      state.commands[name] = f;
      return { dispose() {} };
    },
  },
  tests: {
    createTestController: () => {
      state.controller = {
        items: collection(undefined),
        createTestItem,
        createRunProfile: (label, kind, handler) => (state.profile = handler),
        createTestRun,
        invalidateTestResults: (list) => state.invalidated.push(...(Array.isArray(list) ? list : [list]).map((item) => item.id)),
        dispose() {},
      };
      return state.controller;
    },
  },
};
